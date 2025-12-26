/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef RECURSIVE_PROOF_H
#define RECURSIVE_PROOF_H

#include "basefold_trace.h"
#include "merkle_commitment.h"
#include "gf128.h"

typedef struct {
    // Proof data
    uint8_t *proof_bytes;
    size_t proof_size;
    
    // Metadata
    size_t num_input_proofs;
    double generation_time_ms;
    
    // Commitments
    merkle_commitment_t commitment;
    
    // Sumcheck data
    gf128_t *sumcheck_responses;
    size_t num_sumcheck_rounds;
    
    // Opening proofs
    gf128_t **opening_proofs;
    size_t num_openings;
} recursive_proof_t;

// Function declarations
int generate_recursive_proof(const basefold_proof_t *proof1,
                           const basefold_proof_t *proof2,
                           recursive_proof_t **recursive_proof_out);

int verify_recursive_proof(const recursive_proof_t *rec_proof,
                          const uint8_t *proof1_commitment,
                          const uint8_t *proof2_commitment);

void free_recursive_proof(recursive_proof_t *rec_proof);

#endif /* RECURSIVE_PROOF_H */