/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CONSTRAINT_POLYNOMIAL_H
#define CONSTRAINT_POLYNOMIAL_H

#include <stddef.h>
#include "../../gf128/include/gf128.h"

/**
 * @file constraint_polynomial.h
 * @brief Functions for computing gate constraint polynomials
 */

/**
 * @brief Compute constraint polynomial from gate witness
 * 
 * The gate constraint is: F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O)
 * This function evaluates F at all points given the witness values.
 * 
 * @param witness Gate witness in 4-column format (L, R, O, S)
 * @param num_variables Number of variables (witness size = 2^num_variables)
 * @return Constraint polynomial evaluations, or NULL on error. Caller must free.
 */
gf128_t* compute_constraint_polynomial(const gf128_t* witness, size_t num_variables);

/**
 * @brief Verify that constraint polynomial sums to zero over hypercube
 * 
 * A valid gate constraint polynomial should sum to zero.
 * 
 * @param constraint Constraint polynomial evaluations
 * @param size Size of polynomial
 * @return 0 if sum is zero, -1 otherwise
 */
int verify_constraint_sum_zero(const gf128_t* constraint, size_t size);

#endif /* CONSTRAINT_POLYNOMIAL_H */