/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file gate_witness_generator.c
 * @brief Generate witnesses that satisfy gate constraint sumcheck
 * 
 * The witness must encode valid gate evaluations in the format:
 * - Column 0: Left inputs (L)
 * - Column 1: Right inputs (R)
 * - Column 2: Outputs (O)
 * - Column 3: Selectors (S) - 0 for XOR, 1 for AND
 * 
 * The gate constraint is: F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O) = 0
 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include "../include/basefold_raa.h"
#include "../../gf128/include/gf128.h"
#include "../../circuit_engine/src/evaluator.h"

/**
 * @brief Create a witness from a circuit evaluation trace
 * 
 * This creates a witness where each row represents a gate and the
 * gate constraint F(L,R,O,S) = 0 is satisfied.
 * 
 * @param circuit The circuit to trace
 * @param num_variables Number of variables (must be >= log2(num_gates))
 * @return Witness codeword or NULL on error
 */
gf128_t* generate_gate_constraint_witness(const circuit_t *circuit, size_t num_variables) {
    if (!circuit || num_variables > 30) {
        return NULL;
    }
    
    // The witness size must be 2^num_variables
    size_t witness_size = 1ULL << num_variables;
    
    // Must be divisible by 4 for the 4 columns
    if (witness_size % 4 != 0) {
        return NULL;
    }
    
    size_t num_rows = witness_size / 4;
    
    // Check if we have enough rows for all gates
    if (num_rows < circuit->num_gates) {
        printf("Error: Need at least %u rows for %u gates\n", 
               circuit->num_gates, circuit->num_gates);
        return NULL;
    }
    
    // Allocate witness
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) {
        return NULL;
    }
    
    // Fill in gate evaluations
    for (uint32_t i = 0; i < circuit->num_gates && i < num_rows; i++) {
        const gate_t *gate = &circuit->gates[i];
        
        // For simplicity, set inputs based on wire IDs
        // In a real implementation, these would come from actual wire values
        
        // Left input (L)
        if (gate->input1 == 0) {
            witness[i] = gf128_zero();
        } else if (gate->input1 == 1) {
            witness[i] = gf128_one();
        } else {
            // Use wire ID as a simple value
            uint8_t bytes[16] = {0};
            bytes[0] = (uint8_t)(gate->input1 & 0xFF);
            witness[i] = gf128_from_bytes(bytes);
        }
        
        // Right input (R)
        if (gate->input2 == 0) {
            witness[num_rows + i] = gf128_zero();
        } else if (gate->input2 == 1) {
            witness[num_rows + i] = gf128_one();
        } else {
            uint8_t bytes[16] = {0};
            bytes[0] = (uint8_t)(gate->input2 & 0xFF);
            witness[num_rows + i] = gf128_from_bytes(bytes);
        }
        
        // Compute output (O) based on gate type
        gf128_t L = witness[i];
        gf128_t R = witness[num_rows + i];
        
        if (gate->type == GATE_AND) {
            // O = L * R
            witness[2 * num_rows + i] = gf128_mul(L, R);
            // S = 1 for AND gates
            witness[3 * num_rows + i] = gf128_one();
        } else { // GATE_XOR
            // O = L + R
            witness[2 * num_rows + i] = gf128_add(L, R);
            // S = 0 for XOR gates
            witness[3 * num_rows + i] = gf128_zero();
        }
    }
    
    // Fill remaining rows with valid dummy gates (all zeros is valid: 0 XOR 0 = 0)
    for (size_t i = circuit->num_gates; i < num_rows; i++) {
        witness[i] = gf128_zero();                    // L = 0
        witness[num_rows + i] = gf128_zero();         // R = 0
        witness[2 * num_rows + i] = gf128_zero();     // O = 0
        witness[3 * num_rows + i] = gf128_zero();     // S = 0 (XOR)
        // Constraint: 0*(0*0 - 0) + (1-0)*(0 + 0 - 0) = 0 ✓
    }
    
    return witness;
}

/**
 * @brief Generate a simple test witness with one XOR gate
 * 
 * Creates a witness for: 1 XOR 1 = 0 (in GF(2^128))
 */
gf128_t* generate_simple_xor_witness(size_t num_variables) {
    size_t witness_size = 1ULL << num_variables;
    if (witness_size % 4 != 0) return NULL;
    
    size_t num_rows = witness_size / 4;
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) return NULL;
    
    // First gate: 1 XOR 1 = 0
    witness[0] = gf128_one();                    // L = 1
    witness[num_rows] = gf128_one();             // R = 1  
    witness[2 * num_rows] = gf128_zero();        // O = 0 (1 XOR 1 = 0)
    witness[3 * num_rows] = gf128_zero();        // S = 0 (XOR)
    
    // Rest are dummy gates (0 XOR 0 = 0)
    for (size_t i = 1; i < num_rows; i++) {
        witness[i] = gf128_zero();
        witness[num_rows + i] = gf128_zero();
        witness[2 * num_rows + i] = gf128_zero();
        witness[3 * num_rows + i] = gf128_zero();
    }
    
    return witness;
}

/**
 * @brief Generate a witness with multiple gates
 */
gf128_t* generate_multi_gate_witness(size_t num_variables) {
    size_t witness_size = 1ULL << num_variables;
    if (witness_size % 4 != 0) return NULL;
    
    size_t num_rows = witness_size / 4;
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) return NULL;
    
    // Gate 0: 1 AND 1 = 1
    witness[0] = gf128_one();                    // L = 1
    witness[num_rows] = gf128_one();             // R = 1
    witness[2 * num_rows] = gf128_one();         // O = 1 
    witness[3 * num_rows] = gf128_one();         // S = 1 (AND)
    
    // Gate 1: 0 XOR 1 = 1
    witness[1] = gf128_zero();                   // L = 0
    witness[num_rows + 1] = gf128_one();         // R = 1
    witness[2 * num_rows + 1] = gf128_one();     // O = 1
    witness[3 * num_rows + 1] = gf128_zero();    // S = 0 (XOR)
    
    // Gate 2: Result of gate 0 AND result of gate 1 = 1 AND 1 = 1
    witness[2] = witness[2 * num_rows];          // L = output of gate 0
    witness[num_rows + 2] = witness[2 * num_rows + 1]; // R = output of gate 1
    witness[2 * num_rows + 2] = gf128_one();     // O = 1
    witness[3 * num_rows + 2] = gf128_one();     // S = 1 (AND)
    
    // Fill rest with dummy gates
    for (size_t i = 3; i < num_rows; i++) {
        witness[i] = gf128_zero();
        witness[num_rows + i] = gf128_zero();
        witness[2 * num_rows + i] = gf128_zero();
        witness[3 * num_rows + i] = gf128_zero();
    }
    
    return witness;
}

/**
 * @brief Verify that a witness satisfies gate constraints
 * 
 * For debugging - checks that F(L,R,O,S) = 0 for all gates
 */
int verify_gate_constraints(const gf128_t *witness, size_t witness_size) {
    if (witness_size % 4 != 0) return -1;
    
    size_t num_rows = witness_size / 4;
    int valid = 1;
    
    for (size_t i = 0; i < num_rows; i++) {
        gf128_t L = witness[i];
        gf128_t R = witness[num_rows + i];
        gf128_t O = witness[2 * num_rows + i];
        gf128_t S = witness[3 * num_rows + i];
        
        // Check F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O)
        gf128_t lr = gf128_mul(L, R);
        gf128_t lr_minus_o = gf128_add(lr, O);
        gf128_t and_term = gf128_mul(S, lr_minus_o);
        
        gf128_t l_plus_r = gf128_add(L, R);
        gf128_t lxorr_minus_o = gf128_add(l_plus_r, O);
        gf128_t one = gf128_one();
        gf128_t one_minus_s = gf128_add(one, S);
        gf128_t xor_term = gf128_mul(one_minus_s, lxorr_minus_o);
        
        gf128_t result = gf128_add(and_term, xor_term);
        
        if (!gf128_eq(result, gf128_zero())) {
            printf("Gate %zu constraint not satisfied!\n", i);
            valid = 0;
        }
    }
    
    return valid ? 0 : -1;
}