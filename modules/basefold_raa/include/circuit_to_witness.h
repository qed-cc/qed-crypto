/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CIRCUIT_TO_WITNESS_H
#define CIRCUIT_TO_WITNESS_H

#include <stddef.h>
#include "../../gf128/include/gf128.h"
#include "../../circuit_engine/src/evaluator.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Convert evaluated circuit to gate witness format.
 *
 * The witness format is a 4-column structure:
 * - Column 0: L (left inputs) at indices [0, num_rows)
 * - Column 1: R (right inputs) at indices [num_rows, 2*num_rows)
 * - Column 2: O (outputs) at indices [2*num_rows, 3*num_rows)
 * - Column 3: S (selectors) at indices [3*num_rows, 4*num_rows)
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
);

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
);

/**
 * @brief Free witness memory
 */
void free_witness(gf128_t* witness);

#ifdef __cplusplus
}
#endif

#endif /* CIRCUIT_TO_WITNESS_H */
