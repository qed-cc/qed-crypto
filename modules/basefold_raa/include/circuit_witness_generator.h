/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CIRCUIT_WITNESS_GENERATOR_H
#define CIRCUIT_WITNESS_GENERATOR_H

#include <stddef.h>
#include "../../gf128/include/gf128.h"
#include "../../circuit_engine/src/evaluator.h"

/**
 * @file circuit_witness_generator.h
 * @brief Generate valid witnesses for circuits that satisfy sumcheck
 */

/**
 * @brief Generate witness by evaluating circuit on all 2^n inputs
 * 
 * @param circuit Circuit to evaluate
 * @param num_variables Number of input variables (log2 of witness size)
 * @return Witness polynomial or NULL on error
 */
gf128_t* generate_circuit_witness(const circuit_t *circuit, size_t num_variables);

/**
 * @brief Generate witness for identity circuit (for testing)
 * @return Witness where f(x0, x1, ..., xn) = x0
 */
gf128_t* generate_identity_witness(size_t num_variables);

/**
 * @brief Generate witness for AND of all inputs
 * @return Witness where f(x0, x1, ..., xn) = x0 AND x1 AND ... AND xn
 */
gf128_t* generate_and_all_witness(size_t num_variables);

/**
 * @brief Create a simple test circuit
 * @return Circuit computing out = in0 XOR in1
 */
circuit_t* create_simple_test_circuit(void);

#endif /* CIRCUIT_WITNESS_GENERATOR_H */