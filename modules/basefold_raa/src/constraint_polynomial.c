/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdlib.h>
#include <string.h>
#include "../../gf128/include/gf128.h"

/**
 * @file constraint_polynomial.c
 * @brief Compute constraint polynomial from gate witness
 * 
 * The gate constraint is: F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O)
 * In GF(2^128), subtraction is XOR, so:
 * F(L,R,O,S) = S*(L*R + O) + (1+S)*(L + R + O)
 */

/**
 * @brief Compute constraint polynomial from gate witness
 * 
 * @param witness Gate witness in 4-column format (L, R, O, S)
 * @param num_variables Number of variables (witness size = 2^num_variables)
 * @return Constraint polynomial evaluations, or NULL on error
 * 
 * The witness is structured as 4 columns:
 * - Column 0: L (left inputs) at indices [0, num_rows)
 * - Column 1: R (right inputs) at indices [num_rows, 2*num_rows)
 * - Column 2: O (outputs) at indices [2*num_rows, 3*num_rows)
 * - Column 3: S (selectors) at indices [3*num_rows, 4*num_rows)
 * 
 * The output is the constraint polynomial F evaluated at each point.
 */
gf128_t* compute_constraint_polynomial(const gf128_t* witness, size_t num_variables) {
    if (!witness || num_variables < 2) {
        return NULL;
    }
    
    size_t witness_size = 1ULL << num_variables;
    size_t num_rows = witness_size / 4;
    
    // Allocate space for constraint polynomial
    gf128_t* constraint = calloc(witness_size, sizeof(gf128_t));
    if (!constraint) {
        return NULL;
    }
    
    // For each gate, compute the constraint value
    for (size_t i = 0; i < num_rows; i++) {
        gf128_t L = witness[i];
        gf128_t R = witness[num_rows + i];
        gf128_t O = witness[2 * num_rows + i];
        gf128_t S = witness[3 * num_rows + i];
        
        // Compute S*(L*R + O)
        gf128_t mul_gate = gf128_add(gf128_mul(L, R), O);
        gf128_t term1 = gf128_mul(S, mul_gate);
        
        // Compute (1+S)*(L + R + O)
        gf128_t one_plus_s = gf128_add(gf128_one(), S);
        gf128_t add_gate = gf128_add(gf128_add(L, R), O);
        gf128_t term2 = gf128_mul(one_plus_s, add_gate);
        
        // F = term1 + term2
        constraint[i] = gf128_add(term1, term2);
    }
    
    // The remaining elements stay zero (padded)
    
    return constraint;
}

/**
 * @brief Verify that constraint polynomial sums to zero
 * 
 * @param constraint Constraint polynomial evaluations
 * @param size Size of polynomial
 * @return 0 if sum is zero, -1 otherwise
 */
int verify_constraint_sum_zero(const gf128_t* constraint, size_t size) {
    if (!constraint) {
        return -1;
    }
    
    gf128_t sum = gf128_zero();
    for (size_t i = 0; i < size; i++) {
        sum = gf128_add(sum, constraint[i]);
    }
    
    return gf128_is_zero(sum) ? 0 : -1;
}