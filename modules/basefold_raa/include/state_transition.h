/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef STATE_TRANSITION_H
#define STATE_TRANSITION_H

#include <stdint.h>
#include <stddef.h>
#include "../../circuit_evaluator/include/evaluator.h"

/**
 * @file state_transition.h
 * @brief State transition circuits for blockchain circular recursion
 */

/**
 * Blockchain state for circuits
 */
typedef struct {
    uint8_t prev_hash[32];      /**< Previous block hash */
    uint64_t block_number;      /**< Current block number */
    uint64_t total_work;        /**< Accumulated work */
    uint8_t data[32];           /**< Block data/transactions */
} blockchain_circuit_state_t;

/**
 * @brief Create a simple state transition circuit
 * 
 * Circuit computes: new_hash = SHA3(prev_hash || block_number || data)
 * 
 * @param prev_state Previous blockchain state
 * @param new_state New blockchain state
 * @return Created circuit or NULL on error
 */
circuit_t* create_state_transition_circuit(
    const blockchain_circuit_state_t *prev_state,
    const blockchain_circuit_state_t *new_state
);

/**
 * @brief Create a recursive state transition circuit
 * 
 * This circuit additionally verifies the previous proof
 * 
 * @param prev_state Previous blockchain state
 * @param new_state New blockchain state  
 * @param proof_size Size of proof to verify
 * @return Created circuit or NULL on error
 */
circuit_t* create_recursive_state_transition_circuit(
    const blockchain_circuit_state_t *prev_state,
    const blockchain_circuit_state_t *new_state,
    size_t proof_size
);

/**
 * @brief Free state transition circuit
 * 
 * @param circuit Circuit to free
 */
void free_state_transition_circuit(circuit_t *circuit);

#endif /* STATE_TRANSITION_H */