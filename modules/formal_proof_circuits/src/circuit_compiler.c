/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#include "../include/formal_proof_circuits.h"
#include "../include/gate_types.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/**
 * @file circuit_compiler.c
 * @brief Compile logical formulas to arithmetic circuits over GF(2^128)
 * 
 * Key insight: Boolean logic maps perfectly to GF(2^128) when restricted to {0,1}:
 * - NOT p = 1 - p
 * - p AND q = p * q  
 * - p OR q = p + q - p*q
 * - p XOR q = p + q (in GF(2^128))
 * - p IMPLIES q = 1 - p + p*q
 * - p IFF q = 1 - (p - q)^2
 */

typedef struct {
    int next_wire;
    int next_gate;
    int max_wires;
    int max_gates;
    
    // Wire allocation
    int* wire_types;  // 0=input, 1=intermediate, 2=output
    char** wire_names;
    
    // Gate storage
    int* gate_types;
    int** gate_inputs;
    int* gate_outputs;
    
    // Variable bindings
    int num_vars;
    char** var_names;
    int* var_wires;
    
    // Constraints
    int num_constraints;
    int* constraints;
} compiler_state_t;

// Forward declarations
static int compile_node(compiler_state_t* state, logic_node_t* node);
static int get_var_wire(compiler_state_t* state, const char* name);
static int alloc_wire(compiler_state_t* state);
static void add_gate(compiler_state_t* state, int type, int* inputs, int num_inputs, int output);

// Initialize compiler state
static compiler_state_t* init_compiler(int max_vars) {
    compiler_state_t* state = calloc(1, sizeof(compiler_state_t));
    
    // Allocate space
    state->max_wires = max_vars * 100;  // Generous allocation
    state->max_gates = max_vars * 50;
    
    state->wire_types = calloc(state->max_wires, sizeof(int));
    state->wire_names = calloc(state->max_wires, sizeof(char*));
    
    state->gate_types = calloc(state->max_gates, sizeof(int));
    state->gate_inputs = calloc(state->max_gates, sizeof(int*));
    state->gate_outputs = calloc(state->max_gates, sizeof(int));
    
    state->var_names = calloc(max_vars, sizeof(char*));
    state->var_wires = calloc(max_vars, sizeof(int));
    
    state->constraints = calloc(state->max_wires, sizeof(int));
    
    return state;
}

// Allocate a new wire
static int alloc_wire(compiler_state_t* state) {
    if (state->next_wire >= state->max_wires) {
        fprintf(stderr, "Too many wires\n");
        return -1;
    }
    return state->next_wire++;
}

// Get or allocate wire for variable
static int get_var_wire(compiler_state_t* state, const char* name) {
    // Search existing variables
    for (int i = 0; i < state->num_vars; i++) {
        if (strcmp(state->var_names[i], name) == 0) {
            return state->var_wires[i];
        }
    }
    
    // Allocate new variable
    int wire = alloc_wire(state);
    state->wire_types[wire] = 0; // input
    state->wire_names[wire] = strdup(name);
    
    state->var_names[state->num_vars] = strdup(name);
    state->var_wires[state->num_vars] = wire;
    state->num_vars++;
    
    return wire;
}

// Add a gate to the circuit
static void add_gate(compiler_state_t* state, int type, int* inputs, int num_inputs, int output) {
    if (state->next_gate >= state->max_gates) {
        fprintf(stderr, "Too many gates\n");
        return;
    }
    
    int g = state->next_gate++;
    state->gate_types[g] = type;
    state->gate_inputs[g] = malloc(num_inputs * sizeof(int));
    memcpy(state->gate_inputs[g], inputs, num_inputs * sizeof(int));
    state->gate_outputs[g] = output;
}

/**
 * Compile NOT gate: output = 1 - input
 */
static int compile_not(compiler_state_t* state, int input) {
    int one_wire = alloc_wire(state);
    int output = alloc_wire(state);
    
    // Create constant 1
    state->wire_types[one_wire] = 0; // input
    state->wire_names[one_wire] = strdup("1");
    
    // output = 1 - input
    int inputs[] = {one_wire, input};
    add_gate(state, GATE_XOR, inputs, 2, output);  // In GF(2), 1-x = 1+x = 1 XOR x
    
    return output;
}

/**
 * Compile AND gate: output = left * right
 */
static int compile_and(compiler_state_t* state, int left, int right) {
    int output = alloc_wire(state);
    int inputs[] = {left, right};
    add_gate(state, GATE_AND, inputs, 2, output);
    return output;
}

/**
 * Compile OR gate: output = left + right - left*right
 * In GF(2^128): = left + right + left*right (since -1 = 1)
 */
static int compile_or(compiler_state_t* state, int left, int right) {
    int product = compile_and(state, left, right);
    int sum = alloc_wire(state);
    int output = alloc_wire(state);
    
    // sum = left + right
    int inputs1[] = {left, right};
    add_gate(state, GATE_XOR, inputs1, 2, sum);
    
    // output = sum + product (which is left + right + left*right in GF(2))
    int inputs2[] = {sum, product};
    add_gate(state, GATE_XOR, inputs2, 2, output);
    
    return output;
}

/**
 * Compile XOR gate: output = left + right (in GF(2^128))
 */
static int compile_xor(compiler_state_t* state, int left, int right) {
    int output = alloc_wire(state);
    int inputs[] = {left, right};
    add_gate(state, GATE_XOR, inputs, 2, output);
    return output;
}

/**
 * Compile IMPLIES: p → q = ¬p ∨ q = 1 - p + p*q
 */
static int compile_implies(compiler_state_t* state, int p, int q) {
    int not_p = compile_not(state, p);
    return compile_or(state, not_p, q);
}

/**
 * Compile IFF (if and only if): p ↔ q = (p → q) ∧ (q → p)
 * Optimized: = 1 - (p - q)^2 in fields of characteristic 2
 * But in GF(2), simpler: p ↔ q = 1 - (p XOR q)
 */
static int compile_iff(compiler_state_t* state, int p, int q) {
    int xor_result = compile_xor(state, p, q);
    return compile_not(state, xor_result);
}

/**
 * Compile equality test
 */
static int compile_eq(compiler_state_t* state, int left, int right) {
    // For values in {0,1}, equality is same as IFF
    return compile_iff(state, left, right);
}

/**
 * Compile less than (for bounded integers)
 * For single bits: p < q = ¬p ∧ q
 */
static int compile_lt(compiler_state_t* state, int left, int right) {
    int not_left = compile_not(state, left);
    return compile_and(state, not_left, right);
}

/**
 * Compile greater than
 * For single bits: p > q = p ∧ ¬q
 */
static int compile_gt(compiler_state_t* state, int left, int right) {
    int not_right = compile_not(state, right);
    return compile_and(state, left, not_right);
}

/**
 * Compile universal quantification
 * ∀x. P(x) becomes: ∏_{x∈Domain} P(x) = 1
 * For small domains, we expand. For large domains, use sumcheck.
 */
static int compile_forall(compiler_state_t* state, logic_node_t* var, logic_node_t* body, int domain_size) {
    if (domain_size <= 16) {
        // Small domain: expand explicitly
        int result = -1;
        
        for (int i = 0; i < domain_size; i++) {
            // Bind variable to value i
            char val_name[32];
            snprintf(val_name, sizeof(val_name), "%s_%d", var->name, i);
            int old_wire = get_var_wire(state, var->name);
            
            // Temporarily bind to constant
            for (int j = 0; j < state->num_vars; j++) {
                if (strcmp(state->var_names[j], var->name) == 0) {
                    state->var_wires[j] = alloc_wire(state);
                    state->wire_types[state->var_wires[j]] = 0; // input
                    state->wire_names[state->var_wires[j]] = strdup(val_name);
                    break;
                }
            }
            
            // Compile body with this binding
            int body_result = compile_node(state, body);
            
            // Accumulate with AND
            if (result == -1) {
                result = body_result;
            } else {
                result = compile_and(state, result, body_result);
            }
        }
        
        return result;
    } else {
        // Large domain: use polynomial constraints
        // This requires more sophisticated handling
        fprintf(stderr, "Large domain quantification not yet implemented\n");
        return -1;
    }
}

/**
 * Compile existential quantification
 * ∃x. P(x) becomes: ∑_{x∈Domain} P(x) ≥ 1
 * For small domains, we expand. For large domains, use witness.
 */
static int compile_exists(compiler_state_t* state, logic_node_t* var, logic_node_t* body, int domain_size) {
    if (domain_size <= 16) {
        // Small domain: expand to OR
        int result = -1;
        
        for (int i = 0; i < domain_size; i++) {
            // Similar to forall, but use OR
            char val_name[32];
            snprintf(val_name, sizeof(val_name), "%s_%d", var->name, i);
            
            // Bind variable (same as forall)
            // ... (binding code)
            
            int body_result = compile_node(state, body);
            
            if (result == -1) {
                result = body_result;
            } else {
                result = compile_or(state, result, body_result);
            }
        }
        
        return result;
    } else {
        // Large domain: require witness
        fprintf(stderr, "Large domain existential not yet implemented\n");
        return -1;
    }
}

/**
 * Main compilation function
 */
static int compile_node(compiler_state_t* state, logic_node_t* node) {
    if (!node) return -1;
    
    switch (node->type) {
        case LOGIC_VAR:
            return get_var_wire(state, node->name);
            
        case LOGIC_NOT:
            return compile_not(state, compile_node(state, node->left));
            
        case LOGIC_AND:
            return compile_and(state, 
                             compile_node(state, node->left),
                             compile_node(state, node->right));
            
        case LOGIC_OR:
            return compile_or(state,
                            compile_node(state, node->left),
                            compile_node(state, node->right));
            
        case LOGIC_XOR:
            return compile_xor(state,
                             compile_node(state, node->left),
                             compile_node(state, node->right));
            
        case LOGIC_IMPLIES:
            return compile_implies(state,
                                 compile_node(state, node->left),
                                 compile_node(state, node->right));
            
        case LOGIC_IFF:
            return compile_iff(state,
                             compile_node(state, node->left),
                             compile_node(state, node->right));
            
        case LOGIC_EQ:
            return compile_eq(state,
                            compile_node(state, node->left),
                            compile_node(state, node->right));
            
        case LOGIC_LT:
            return compile_lt(state,
                            compile_node(state, node->left),
                            compile_node(state, node->right));
            
        case LOGIC_GT:
            return compile_gt(state,
                            compile_node(state, node->left),
                            compile_node(state, node->right));
            
        case LOGIC_FORALL:
            // Default to small domain for now
            return compile_forall(state, node->quantified, node->left, 2);
            
        case LOGIC_EXISTS:
            return compile_exists(state, node->quantified, node->left, 2);
            
        case LOGIC_PRED:
            // For now, predicates are just variables
            return get_var_wire(state, node->name);
            
        default:
            fprintf(stderr, "Unknown node type: %d\n", node->type);
            return -1;
    }
}

/**
 * Public API: Compile formula to circuit
 */
proof_circuit_t* compile_to_circuit(logic_node_t* formula) {
    if (!formula) return NULL;
    
    // Initialize compiler
    compiler_state_t* state = init_compiler(100);
    
    // Compile the formula
    int result_wire = compile_node(state, formula);
    if (result_wire < 0) {
        // TODO: cleanup
        return NULL;
    }
    
    // Add constraint that result must be 1
    state->constraints[state->num_constraints++] = result_wire;
    
    // Build circuit structure
    proof_circuit_t* circuit = calloc(1, sizeof(proof_circuit_t));
    
    // Count inputs (variables and constants)
    circuit->num_inputs = 0;
    for (int i = 0; i < state->next_wire; i++) {
        if (state->wire_types[i] == 0) {
            circuit->num_inputs++;
        }
    }
    
    circuit->num_outputs = state->num_constraints;
    circuit->num_gates = state->next_gate;
    circuit->num_wires = state->next_wire;
    
    // Copy gate data
    circuit->gate_type = malloc(circuit->num_gates * sizeof(int));
    circuit->gate_inputs = malloc(circuit->num_gates * sizeof(int*));
    circuit->gate_output = malloc(circuit->num_gates * sizeof(int));
    
    for (int i = 0; i < circuit->num_gates; i++) {
        circuit->gate_type[i] = state->gate_types[i];
        
        // Count inputs for this gate
        int num_inputs = 2; // Most gates are binary
        circuit->gate_inputs[i] = malloc(num_inputs * sizeof(int));
        memcpy(circuit->gate_inputs[i], state->gate_inputs[i], num_inputs * sizeof(int));
        
        circuit->gate_output[i] = state->gate_outputs[i];
    }
    
    // Copy constraints
    circuit->num_constraints = state->num_constraints;
    circuit->constraint_wires = malloc(circuit->num_constraints * sizeof(int));
    memcpy(circuit->constraint_wires, state->constraints, circuit->num_constraints * sizeof(int));
    
    // TODO: cleanup state
    
    return circuit;
}

/**
 * Debug: Print circuit
 */
void print_circuit(proof_circuit_t* circuit) {
    printf("Circuit: %d inputs, %d outputs, %d gates, %d wires\n",
           circuit->num_inputs, circuit->num_outputs, 
           circuit->num_gates, circuit->num_wires);
    
    for (int i = 0; i < circuit->num_gates; i++) {
        const char* gate_names[] = {"AND", "OR", "NOT", "XOR", "IMPLIES", "IFF"};
        printf("Gate %d: %s, inputs=[%d,%d], output=%d\n",
               i, gate_names[circuit->gate_type[i]],
               circuit->gate_inputs[i][0],
               circuit->gate_inputs[i][1],
               circuit->gate_output[i]);
    }
    
    printf("Constraints: ");
    for (int i = 0; i < circuit->num_constraints; i++) {
        printf("wire_%d=1 ", circuit->constraint_wires[i]);
    }
    printf("\n");
}