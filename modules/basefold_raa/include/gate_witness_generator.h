/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef GATE_WITNESS_GENERATOR_H
#define GATE_WITNESS_GENERATOR_H

#include <stddef.h>
#include "../../gf128/include/gf128.h"
#include "../../circuit_evaluator/include/evaluator.h"

/**
 * @file gate_witness_generator.h
 * @brief Generate witnesses that satisfy gate constraint sumcheck
 */

/**
 * @brief Create a witness from a circuit evaluation trace
 * 
 * @param circuit The circuit to trace
 * @param num_variables Number of variables (must be >= log2(4*num_gates))
 * @return Witness codeword or NULL on error
 */
gf128_t* generate_gate_constraint_witness(const circuit_t *circuit, size_t num_variables);

/**
 * @brief Generate a simple test witness with one XOR gate
 * @param num_variables Number of variables
 * @return Witness for: 1 XOR 1 = 0
 */
gf128_t* generate_simple_xor_witness(size_t num_variables);

/**
 * @brief Generate a witness with multiple gates
 * @param num_variables Number of variables
 * @return Witness with AND and XOR gates
 */
gf128_t* generate_multi_gate_witness(size_t num_variables);

/**
 * @brief Verify that a witness satisfies gate constraints
 * @param witness The witness to verify
 * @param witness_size Size of witness
 * @return 0 if valid, -1 if invalid
 */
int verify_gate_constraints(const gf128_t *witness, size_t witness_size);

#endif /* GATE_WITNESS_GENERATOR_H */