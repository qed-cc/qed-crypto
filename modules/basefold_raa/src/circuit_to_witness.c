/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "../../gf128/include/gf128.h"
#include "../../circuit_engine/src/evaluator.h"

/**
 * @file circuit_to_witness.c
 * @brief Convert evaluated circuit to gate witness format for STARK proving
 *
 * The witness format is a 4-column structure:
 * - Column 0: L (left inputs) at indices [0, num_rows)
 * - Column 1: R (right inputs) at indices [num_rows, 2*num_rows)
 * - Column 2: O (outputs) at indices [2*num_rows, 3*num_rows)
 * - Column 3: S (selectors) at indices [3*num_rows, 4*num_rows)
 *
 * The gate constraint is: F(L,R,O,S) = S*(L*R + O) + (1+S)*(L + R + O)
 * For valid circuits, F evaluates to zero at every row.
 */

/**
 * @brief Round up to next power of 2
 */
static size_t next_power_of_2(size_t n) {
    if (n == 0) return 1;
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n |= n >> 32;
    return n + 1;
}

/**
 * @brief Compute log2 of a power of 2
 */
static size_t log2_of_pow2(size_t n) {
    size_t log = 0;
    while (n > 1) {
        n >>= 1;
        log++;
    }
    return log;
}

/**
 * @brief Convert evaluated circuit to gate witness format.
 *
 * @param circuit     Evaluated circuit with gates
 * @param wire_state  Wire values from evaluation
 * @param witness_out Output: GF(2^128) array of size 2^num_variables
 * @param num_vars    Output: log2(witness_size)
 * @return 0 on success, negative on error
 */
int circuit_to_witness(
    const circuit_t* circuit,
    const wire_state_t* wire_state,
    gf128_t** witness_out,
    size_t* num_vars
) {
    if (!circuit || !wire_state || !witness_out || !num_vars) {
        return -1;
    }

    if (circuit->num_gates == 0) {
        return -2;
    }

    size_t num_gates = circuit->num_gates;

    /* Round up to power of 2 for the number of rows */
    size_t num_rows = next_power_of_2(num_gates);

    /* Total witness size is 4 columns * num_rows */
    size_t witness_size = num_rows * 4;

    *num_vars = log2_of_pow2(witness_size);

    /* Allocate witness with zero initialization */
    gf128_t* witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) {
        return -3;
    }

    /* Fill in witness values from circuit */
    for (size_t i = 0; i < num_gates; i++) {
        gate_t* gate = &circuit->gates[i];

        /* Get wire values (0 or 1) */
        uint8_t l_val = wire_state->values[gate->input1];
        uint8_t r_val = wire_state->values[gate->input2];
        uint8_t o_val = wire_state->values[gate->output];

        /* L column: left input value */
        witness[i] = l_val ? gf128_one() : gf128_zero();

        /* R column: right input value */
        witness[num_rows + i] = r_val ? gf128_one() : gf128_zero();

        /* O column: output value */
        witness[2 * num_rows + i] = o_val ? gf128_one() : gf128_zero();

        /* S column: selector (1 for AND, 0 for XOR) */
        witness[3 * num_rows + i] = (gate->type == GATE_AND) ? gf128_one() : gf128_zero();
    }

    /* Padding rows stay zero (already calloc'd) */

    *witness_out = witness;
    return 0;
}

/**
 * @brief Verify that witness satisfies gate constraints
 *
 * @param witness     Gate witness in 4-column format
 * @param num_vars    Number of variables (witness size = 2^num_vars)
 * @param num_gates   Actual number of gates (non-padding rows)
 * @return 0 if all constraints satisfied, negative otherwise
 */
int verify_witness_constraints(
    const gf128_t* witness,
    size_t num_vars,
    size_t num_gates
) {
    if (!witness || num_vars < 2) {
        return -1;
    }

    size_t witness_size = 1ULL << num_vars;
    size_t num_rows = witness_size / 4;

    /* Check each gate */
    for (size_t i = 0; i < num_gates; i++) {
        gf128_t L = witness[i];
        gf128_t R = witness[num_rows + i];
        gf128_t O = witness[2 * num_rows + i];
        gf128_t S = witness[3 * num_rows + i];

        /* Compute F(L,R,O,S) = S*(L*R + O) + (1+S)*(L + R + O) */
        gf128_t mul_gate = gf128_add(gf128_mul(L, R), O);
        gf128_t term1 = gf128_mul(S, mul_gate);

        gf128_t one_plus_s = gf128_add(gf128_one(), S);
        gf128_t add_gate = gf128_add(gf128_add(L, R), O);
        gf128_t term2 = gf128_mul(one_plus_s, add_gate);

        gf128_t constraint = gf128_add(term1, term2);

        if (!gf128_is_zero(constraint)) {
            fprintf(stderr, "Constraint violation at gate %zu\n", i);
            return -2;
        }
    }

    return 0;
}

/**
 * @brief Free witness memory
 */
void free_witness(gf128_t* witness) {
    if (witness) {
        free(witness);
    }
}
