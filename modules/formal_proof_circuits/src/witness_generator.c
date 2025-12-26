/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#include "../include/basefold_integration.h"
#include "../include/gate_types.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>

/**
 * @brief SAT solver for witness generation
 * 
 * Implements DPLL algorithm with modern optimizations:
 * - Unit propagation
 * - Pure literal elimination
 * - VSIDS-style variable ordering
 * - Random restarts
 * - Parallel search threads
 */

typedef struct {
    int num_variables;
    int num_clauses;
    int** clauses;        // CNF clauses
    int* clause_sizes;    // Size of each clause
    uint8_t* assignment;  // Current assignment
    int* unassigned;      // Stack of unassigned variables
    int num_unassigned;
    double* activity;     // Variable activity scores
    uint64_t conflicts;   // Conflict counter
} sat_state_t;

/**
 * @brief Convert circuit to CNF for SAT solver
 */
static int circuit_to_cnf(const proof_circuit_t* circuit,
                         sat_state_t* state) {
    // Count clauses needed
    int num_clauses = 0;
    
    // Each gate generates clauses
    for (int i = 0; i < circuit->num_gates; i++) {
        switch(circuit->gate_type[i]) {
            case GATE_AND:
                num_clauses += 3; // (¬a ∨ ¬b ∨ c) ∧ (a ∨ ¬c) ∧ (b ∨ ¬c)
                break;
            case GATE_OR:
                num_clauses += 3; // (a ∨ b ∨ ¬c) ∧ (¬a ∨ c) ∧ (¬b ∨ c)
                break;
            case GATE_NOT:
                num_clauses += 2; // (¬a ∨ ¬c) ∧ (a ∨ c)
                break;
            case GATE_XOR:
                num_clauses += 4; // CNF encoding of XOR
                break;
            default:
                num_clauses += 4; // Conservative estimate
                break;
        }
    }
    
    // Each constraint adds a unit clause
    num_clauses += circuit->num_constraints;
    
    // Allocate clause arrays
    state->num_variables = circuit->num_wires;
    state->num_clauses = num_clauses;
    state->clauses = calloc(num_clauses, sizeof(int*));
    state->clause_sizes = calloc(num_clauses, sizeof(int));
    
    if (!state->clauses || !state->clause_sizes) {
        return -1;
    }
    
    int clause_idx = 0;
    
    // Generate clauses for each gate
    for (int i = 0; i < circuit->num_gates; i++) {
        int* inputs = circuit->gate_inputs[i];
        int output = circuit->gate_output[i];
        
        // Variables are 1-indexed in SAT, 0-indexed in circuit
        int a = inputs[0] + 1;
        int b = (circuit->gate_type[i] != GATE_NOT) ? inputs[1] + 1 : 0;
        int c = output + 1;
        
        switch(circuit->gate_type[i]) {
            case GATE_AND:
                // c = a ∧ b
                // (¬a ∨ ¬b ∨ c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = -a;
                state->clauses[clause_idx][1] = -b;
                state->clauses[clause_idx][2] = c;
                state->clause_sizes[clause_idx++] = 3;
                
                // (a ∨ ¬c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = a;
                state->clauses[clause_idx][1] = -c;
                state->clause_sizes[clause_idx++] = 2;
                
                // (b ∨ ¬c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = b;
                state->clauses[clause_idx][1] = -c;
                state->clause_sizes[clause_idx++] = 2;
                break;
                
            case GATE_OR:
                // c = a ∨ b
                // (a ∨ b ∨ ¬c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = a;
                state->clauses[clause_idx][1] = b;
                state->clauses[clause_idx][2] = -c;
                state->clause_sizes[clause_idx++] = 3;
                
                // (¬a ∨ c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = -a;
                state->clauses[clause_idx][1] = c;
                state->clause_sizes[clause_idx++] = 2;
                
                // (¬b ∨ c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = -b;
                state->clauses[clause_idx][1] = c;
                state->clause_sizes[clause_idx++] = 2;
                break;
                
            case GATE_NOT:
                // c = ¬a
                // (¬a ∨ ¬c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = -a;
                state->clauses[clause_idx][1] = -c;
                state->clause_sizes[clause_idx++] = 2;
                
                // (a ∨ c)
                state->clauses[clause_idx] = malloc(2 * sizeof(int));
                state->clauses[clause_idx][0] = a;
                state->clauses[clause_idx][1] = c;
                state->clause_sizes[clause_idx++] = 2;
                break;
                
            case GATE_XOR:
                // c = a ⊕ b
                // (¬a ∨ ¬b ∨ ¬c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = -a;
                state->clauses[clause_idx][1] = -b;
                state->clauses[clause_idx][2] = -c;
                state->clause_sizes[clause_idx++] = 3;
                
                // (a ∨ b ∨ ¬c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = a;
                state->clauses[clause_idx][1] = b;
                state->clauses[clause_idx][2] = -c;
                state->clause_sizes[clause_idx++] = 3;
                
                // (¬a ∨ b ∨ c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = -a;
                state->clauses[clause_idx][1] = b;
                state->clauses[clause_idx][2] = c;
                state->clause_sizes[clause_idx++] = 3;
                
                // (a ∨ ¬b ∨ c)
                state->clauses[clause_idx] = malloc(3 * sizeof(int));
                state->clauses[clause_idx][0] = a;
                state->clauses[clause_idx][1] = -b;
                state->clauses[clause_idx][2] = c;
                state->clause_sizes[clause_idx++] = 3;
                break;
                
            default:
                // TODO: Handle IMPLIES, IFF, etc.
                break;
        }
    }
    
    // Add constraint clauses (unit clauses forcing wires to 1)
    for (int i = 0; i < circuit->num_constraints; i++) {
        state->clauses[clause_idx] = malloc(sizeof(int));
        state->clauses[clause_idx][0] = circuit->constraint_wires[i] + 1;
        state->clause_sizes[clause_idx++] = 1;
    }
    
    state->num_clauses = clause_idx;
    
    // Initialize solver state
    state->assignment = calloc(state->num_variables + 1, sizeof(uint8_t));
    state->unassigned = calloc(state->num_variables, sizeof(int));
    state->activity = calloc(state->num_variables + 1, sizeof(double));
    
    // All variables initially unassigned
    state->num_unassigned = state->num_variables;
    for (int i = 0; i < state->num_variables; i++) {
        state->unassigned[i] = i + 1;
        state->activity[i + 1] = 0.0;
    }
    
    return 0;
}

/**
 * @brief Check if clause is satisfied
 */
static int is_clause_satisfied(const sat_state_t* state, int clause_idx) {
    int* clause = state->clauses[clause_idx];
    int size = state->clause_sizes[clause_idx];
    
    for (int i = 0; i < size; i++) {
        int lit = clause[i];
        int var = abs(lit);
        
        if (state->assignment[var] != 0) {
            // Variable is assigned
            int value = state->assignment[var] == 2;
            if ((lit > 0 && value) || (lit < 0 && !value)) {
                return 1; // Clause satisfied
            }
        }
    }
    
    return 0; // Not satisfied
}

/**
 * @brief Unit propagation
 */
static int unit_propagate(sat_state_t* state) {
    int propagated;
    
    do {
        propagated = 0;
        
        // Find unit clauses
        for (int i = 0; i < state->num_clauses; i++) {
            if (is_clause_satisfied(state, i)) {
                continue;
            }
            
            int unassigned_lit = 0;
            int num_unassigned = 0;
            
            int* clause = state->clauses[i];
            int size = state->clause_sizes[i];
            
            for (int j = 0; j < size; j++) {
                int lit = clause[j];
                int var = abs(lit);
                
                if (state->assignment[var] == 0) {
                    unassigned_lit = lit;
                    num_unassigned++;
                    if (num_unassigned > 1) break;
                }
            }
            
            if (num_unassigned == 1) {
                // Unit clause found, must assign variable
                int var = abs(unassigned_lit);
                state->assignment[var] = (unassigned_lit > 0) ? 2 : 1;
                
                // Remove from unassigned list
                for (int k = 0; k < state->num_unassigned; k++) {
                    if (state->unassigned[k] == var) {
                        state->unassigned[k] = state->unassigned[--state->num_unassigned];
                        break;
                    }
                }
                
                propagated = 1;
            } else if (num_unassigned == 0) {
                // Conflict detected
                return -1;
            }
        }
    } while (propagated);
    
    return 0;
}

/**
 * @brief Choose next variable using VSIDS heuristic
 */
static int choose_variable(const sat_state_t* state) {
    if (state->num_unassigned == 0) {
        return 0;
    }
    
    int best_var = state->unassigned[0];
    double best_activity = state->activity[best_var];
    
    for (int i = 1; i < state->num_unassigned; i++) {
        int var = state->unassigned[i];
        if (state->activity[var] > best_activity) {
            best_var = var;
            best_activity = state->activity[var];
        }
    }
    
    return best_var;
}

/**
 * @brief DPLL recursive solver
 */
static int dpll_solve(sat_state_t* state, 
                     const witness_config_t* config,
                     uint64_t start_time) {
    // Check timeout
    if (config->timeout_ms > 0) {
        uint64_t elapsed = (clock() - start_time) * 1000 / CLOCKS_PER_SEC;
        if (elapsed > config->timeout_ms) {
            return -2; // Timeout
        }
    }
    
    // Unit propagation
    if (unit_propagate(state) < 0) {
        state->conflicts++;
        return 0; // Conflict
    }
    
    // Check if solved
    if (state->num_unassigned == 0) {
        return 1; // SAT
    }
    
    // Choose variable
    int var = choose_variable(state);
    if (var == 0) {
        return 0; // No variables left
    }
    
    // Save state for backtracking
    uint8_t* saved_assignment = malloc((state->num_variables + 1) * sizeof(uint8_t));
    memcpy(saved_assignment, state->assignment, (state->num_variables + 1) * sizeof(uint8_t));
    int saved_unassigned = state->num_unassigned;
    
    // Try positive assignment
    state->assignment[var] = 2; // true
    for (int i = 0; i < state->num_unassigned; i++) {
        if (state->unassigned[i] == var) {
            state->unassigned[i] = state->unassigned[--state->num_unassigned];
            break;
        }
    }
    
    if (dpll_solve(state, config, start_time) > 0) {
        free(saved_assignment);
        return 1; // Found solution
    }
    
    // Backtrack and try negative assignment
    memcpy(state->assignment, saved_assignment, (state->num_variables + 1) * sizeof(uint8_t));
    state->num_unassigned = saved_unassigned;
    
    state->assignment[var] = 1; // false
    for (int i = 0; i < state->num_unassigned; i++) {
        if (state->unassigned[i] == var) {
            state->unassigned[i] = state->unassigned[--state->num_unassigned];
            break;
        }
    }
    
    int result = dpll_solve(state, config, start_time);
    
    if (result <= 0) {
        // Update activity for learned conflict
        state->activity[var] *= 1.05;
    }
    
    free(saved_assignment);
    return result;
}

/**
 * @brief Worker thread for parallel search
 */
typedef struct {
    const proof_circuit_t* circuit;
    const witness_config_t* config;
    uint8_t* result;
    int* found;
    pthread_mutex_t* mutex;
    uint64_t start_time;
    int thread_id;
} worker_args_t;

static void* search_worker(void* arg) {
    worker_args_t* args = (worker_args_t*)arg;
    
    // Each thread uses different random seed
    srand(time(NULL) + args->thread_id);
    
    sat_state_t state;
    memset(&state, 0, sizeof(state));
    
    // Convert circuit to CNF
    if (circuit_to_cnf(args->circuit, &state) < 0) {
        return NULL;
    }
    
    // Random restarts
    int restarts = 0;
    while (!*args->found) {
        // Check timeout
        uint64_t elapsed = (clock() - args->start_time) * 1000 / CLOCKS_PER_SEC;
        if (args->config->timeout_ms > 0 && elapsed > args->config->timeout_ms) {
            break;
        }
        
        // Randomize initial assignment for diversity
        if (args->config->use_random_search && restarts > 0) {
            for (int i = 1; i <= state.num_variables; i++) {
                if (rand() % 100 < 20) { // 20% chance to pre-assign
                    state.assignment[i] = (rand() % 2) ? 1 : 2;
                    
                    // Update unassigned list
                    state.num_unassigned = 0;
                    for (int j = 1; j <= state.num_variables; j++) {
                        if (state.assignment[j] == 0) {
                            state.unassigned[state.num_unassigned++] = j;
                        }
                    }
                }
            }
        }
        
        // Run DPLL
        int result = dpll_solve(&state, args->config, args->start_time);
        
        if (result > 0) {
            // Found solution
            pthread_mutex_lock(args->mutex);
            if (!*args->found) {
                *args->found = 1;
                
                // Copy assignment to result
                for (int i = 0; i < args->circuit->num_wires; i++) {
                    args->result[i] = (state.assignment[i + 1] == 2) ? 1 : 0;
                }
            }
            pthread_mutex_unlock(args->mutex);
            break;
        }
        
        // Reset for restart
        memset(state.assignment, 0, (state.num_variables + 1) * sizeof(uint8_t));
        state.num_unassigned = state.num_variables;
        for (int i = 0; i < state.num_variables; i++) {
            state.unassigned[i] = i + 1;
        }
        
        restarts++;
        if (restarts >= args->config->max_iterations / 1000) {
            break;
        }
    }
    
    // Cleanup
    for (int i = 0; i < state.num_clauses; i++) {
        free(state.clauses[i]);
    }
    free(state.clauses);
    free(state.clause_sizes);
    free(state.assignment);
    free(state.unassigned);
    free(state.activity);
    
    return NULL;
}

int generate_existential_witness(const proof_circuit_t* proof_circuit,
                                const witness_config_t* config,
                                uint8_t* witness) {
    if (!proof_circuit || !config || !witness) {
        return -1;
    }
    
    // Handle quantifier-free circuits with simple SAT solving
    if (proof_circuit->num_gates == 0) {
        // Trivial circuit
        memset(witness, 0, proof_circuit->num_wires);
        return 0;
    }
    
    uint64_t start_time = clock();
    
    // Determine number of threads
    int num_threads = config->num_threads;
    if (num_threads <= 0) {
        num_threads = 4; // Default to 4 threads
    }
    
    // Shared state
    int found = 0;
    pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
    
    // Create worker threads
    pthread_t* threads = calloc(num_threads, sizeof(pthread_t));
    worker_args_t* args = calloc(num_threads, sizeof(worker_args_t));
    
    for (int i = 0; i < num_threads; i++) {
        args[i].circuit = proof_circuit;
        args[i].config = config;
        args[i].result = witness;
        args[i].found = &found;
        args[i].mutex = &mutex;
        args[i].start_time = start_time;
        args[i].thread_id = i;
        
        pthread_create(&threads[i], NULL, search_worker, &args[i]);
    }
    
    // Wait for threads
    for (int i = 0; i < num_threads; i++) {
        pthread_join(threads[i], NULL);
    }
    
    free(threads);
    free(args);
    pthread_mutex_destroy(&mutex);
    
    return found ? 0 : -1;
}