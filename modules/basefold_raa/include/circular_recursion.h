/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CIRCULAR_RECURSION_H
#define CIRCULAR_RECURSION_H

#include "basefold_raa.h"
#include <stdint.h>
#include <stdbool.h>

/**
 * @file circular_recursion.h
 * @brief Circular recursion for blockchain proofs
 * 
 * Enables proving an entire blockchain with a single proof that
 * recursively verifies all previous state transitions.
 */

/* Blockchain state for circular recursion */
typedef struct {
    uint8_t state_hash[32];      // Current state hash (SHA3-256)
    uint64_t block_number;       // Block number
    uint64_t accumulated_work;   // Total work done
    uint8_t prev_proof_hash[32]; // Hash of previous recursive proof
} blockchain_state_t;

/* Forward declaration */
typedef struct circular_proof circular_proof_t;

/**
 * @brief Generate circular recursion proof
 * 
 * Creates a proof that verifies the entire blockchain history from genesis
 * to the current state. Each proof recursively contains all previous proofs.
 * 
 * @param prev_state Previous blockchain state
 * @param new_state New blockchain state to prove
 * @param prev_proof Previous circular proof (NULL for genesis)
 * @param is_genesis True if this is the first block after genesis
 * @return Circular proof or NULL on error
 */
circular_proof_t* basefold_raa_circular_prove(
    const blockchain_state_t *prev_state,
    const blockchain_state_t *new_state,
    const circular_proof_t *prev_proof,
    bool is_genesis
);

/**
 * @brief Verify circular recursion proof
 * 
 * Verifies that a circular proof correctly proves the entire blockchain
 * history from genesis to the claimed state.
 * 
 * @param cproof Circular proof to verify
 * @param genesis_state Genesis state to verify against
 * @return True if valid, false otherwise
 */
bool basefold_raa_circular_verify(
    const circular_proof_t *cproof,
    const blockchain_state_t *genesis_state
);

/**
 * @brief Free circular proof
 * 
 * @param cproof Circular proof to free
 */
void basefold_raa_circular_free(circular_proof_t *cproof);

/**
 * @brief Get proof size in bytes
 * 
 * @param cproof Circular proof
 * @return Size in bytes
 */
size_t basefold_raa_circular_proof_size(const circular_proof_t *cproof);

#endif /* CIRCULAR_RECURSION_H */