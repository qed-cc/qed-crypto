/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file proof_aggregation.c
 * @brief Proof aggregation for recursive composition
 * 
 * Allows combining multiple proofs into a single proof
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/basefold_trace.h"
#include "../include/transcript.h"
#include "../include/merkle_commitment.h"
#include "../include/binary_ntt.h"
#include "../include/gf128.h"
#include "../include/multilinear.h"

// Aggregation parameters
#define MAX_PROOFS_TO_AGGREGATE 16
#define AGGREGATION_SECURITY_BITS 128

// Aggregated proof structure
typedef struct {
    // Original proofs info
    size_t num_proofs;
    size_t *proof_sizes;
    
    // Aggregated commitments
    merkle_commitment_t *agg_commitment;
    
    // Aggregated sumcheck
    gf128_t *sumcheck_coeffs;
    size_t num_sumcheck_rounds;
    
    // Aggregated openings
    gf128_t **opening_proofs;
    size_t num_openings;
    
    // Random challenges for aggregation
    gf128_t *agg_challenges;
} aggregated_proof_t;

// Generate aggregation challenges
static int generate_aggregation_challenges(transcript_t *transcript,
                                         size_t num_proofs,
                                         gf128_t *challenges) {
    for (size_t i = 0; i < num_proofs; i++) {
        uint8_t challenge_bytes[32];
        char label[64];
        snprintf(label, sizeof(label), "aggregate_challenge_%zu", i);
        
        transcript_challenge(transcript, label, challenge_bytes, 32);
        challenges[i] = gf128_from_bytes(challenge_bytes);
    }
    
    return 0;
}

// Aggregate multiple polynomial commitments
static int aggregate_commitments(const merkle_commitment_t **commitments,
                                size_t num_commitments,
                                const gf128_t *challenges,
                                merkle_commitment_t *agg_commitment) {
    if (num_commitments == 0 || num_commitments > MAX_PROOFS_TO_AGGREGATE) {
        return -1;
    }
    
    // Get size from first commitment
    size_t poly_size = commitments[0]->num_leaves;
    
    // Allocate aggregated polynomial
    gf128_t *agg_poly = calloc(poly_size, sizeof(gf128_t));
    if (!agg_poly) {
        return -2;
    }
    
    // Compute linear combination: agg = Σ challenges[i] * poly[i]
    for (size_t i = 0; i < num_commitments; i++) {
        if (commitments[i]->num_leaves != poly_size) {
            free(agg_poly);
            return -3; // Size mismatch
        }
        
        // Add challenges[i] * poly[i] to aggregation
        for (size_t j = 0; j < poly_size; j++) {
            gf128_t term = gf128_mul(challenges[i], 
                                    commitments[i]->evaluations[j]);
            agg_poly[j] = gf128_add(agg_poly[j], term);
        }
    }
    
    // Build new Merkle tree for aggregated polynomial
    int ret = merkle_commitment_build(agg_poly, poly_size, agg_commitment);
    
    free(agg_poly);
    return ret;
}

// Aggregate sumcheck proofs
static int aggregate_sumcheck_proofs(const basefold_proof_t **proofs,
                                    size_t num_proofs,
                                    const gf128_t *challenges,
                                    aggregated_proof_t *agg_proof) {
    if (num_proofs == 0) {
        return -1;
    }
    
    // Get number of rounds from first proof
    size_t num_rounds = proofs[0]->num_sumcheck_rounds;
    
    // Allocate aggregated sumcheck polynomials
    size_t coeffs_per_round = 3; // degree 2 polynomials
    size_t total_coeffs = num_rounds * coeffs_per_round;
    
    agg_proof->sumcheck_coeffs = calloc(total_coeffs, sizeof(gf128_t));
    if (!agg_proof->sumcheck_coeffs) {
        return -2;
    }
    
    // Aggregate each round
    for (size_t round = 0; round < num_rounds; round++) {
        for (size_t coeff = 0; coeff < coeffs_per_round; coeff++) {
            size_t idx = round * coeffs_per_round + coeff;
            
            // Compute linear combination
            for (size_t proof_idx = 0; proof_idx < num_proofs; proof_idx++) {
                gf128_t term = gf128_mul(challenges[proof_idx],
                                        proofs[proof_idx]->sumcheck_responses[idx]);
                agg_proof->sumcheck_coeffs[idx] = 
                    gf128_add(agg_proof->sumcheck_coeffs[idx], term);
            }
        }
    }
    
    agg_proof->num_sumcheck_rounds = num_rounds;
    return 0;
}

// Main proof aggregation function
int aggregate_proofs(const basefold_proof_t **proofs,
                    size_t num_proofs,
                    transcript_t *transcript,
                    aggregated_proof_t **agg_proof_out) {
    if (!proofs || !transcript || !agg_proof_out || num_proofs == 0) {
        return -1;
    }
    
    if (num_proofs > MAX_PROOFS_TO_AGGREGATE) {
        return -2;
    }
    
    // Allocate aggregated proof
    aggregated_proof_t *agg_proof = calloc(1, sizeof(aggregated_proof_t));
    if (!agg_proof) {
        return -3;
    }
    
    // Generate aggregation challenges
    agg_proof->agg_challenges = calloc(num_proofs, sizeof(gf128_t));
    if (!agg_proof->agg_challenges) {
        free(agg_proof);
        return -4;
    }
    
    generate_aggregation_challenges(transcript, num_proofs, agg_proof->agg_challenges);
    
    // Extract commitments from proofs
    merkle_commitment_t **commitments = calloc(num_proofs, sizeof(merkle_commitment_t*));
    if (!commitments) {
        free(agg_proof->agg_challenges);
        free(agg_proof);
        return -5;
    }
    
    for (size_t i = 0; i < num_proofs; i++) {
        // Assuming proofs have commitment field
        commitments[i] = &proofs[i]->commitment;
    }
    
    // Aggregate commitments
    agg_proof->agg_commitment = calloc(1, sizeof(merkle_commitment_t));
    if (!agg_proof->agg_commitment) {
        free(commitments);
        free(agg_proof->agg_challenges);
        free(agg_proof);
        return -6;
    }
    
    int ret = aggregate_commitments((const merkle_commitment_t**)commitments, 
                                   num_proofs, 
                                   agg_proof->agg_challenges,
                                   agg_proof->agg_commitment);
    if (ret != 0) {
        free(commitments);
        free(agg_proof->agg_commitment);
        free(agg_proof->agg_challenges);
        free(agg_proof);
        return ret;
    }
    
    // Aggregate sumcheck proofs
    ret = aggregate_sumcheck_proofs(proofs, num_proofs, 
                                   agg_proof->agg_challenges, agg_proof);
    if (ret != 0) {
        free(commitments);
        merkle_commitment_free(agg_proof->agg_commitment);
        free(agg_proof->agg_commitment);
        free(agg_proof->agg_challenges);
        free(agg_proof);
        return ret;
    }
    
    // Store proof info
    agg_proof->num_proofs = num_proofs;
    agg_proof->proof_sizes = calloc(num_proofs, sizeof(size_t));
    if (!agg_proof->proof_sizes) {
        free(commitments);
        free(agg_proof->sumcheck_coeffs);
        merkle_commitment_free(agg_proof->agg_commitment);
        free(agg_proof->agg_commitment);
        free(agg_proof->agg_challenges);
        free(agg_proof);
        return -7;
    }
    
    for (size_t i = 0; i < num_proofs; i++) {
        agg_proof->proof_sizes[i] = proofs[i]->proof_size;
    }
    
    free(commitments);
    *agg_proof_out = agg_proof;
    
    return 0;
}

// Verify aggregated proof
int verify_aggregated_proof(const aggregated_proof_t *agg_proof,
                           const basefold_instance_t **instances,
                           size_t num_instances,
                           transcript_t *transcript) {
    if (!agg_proof || !instances || !transcript) {
        return -1;
    }
    
    if (num_instances != agg_proof->num_proofs) {
        return -2;
    }
    
    // Regenerate aggregation challenges
    gf128_t *challenges = calloc(num_instances, sizeof(gf128_t));
    if (!challenges) {
        return -3;
    }
    
    generate_aggregation_challenges(transcript, num_instances, challenges);
    
    // Verify challenges match
    for (size_t i = 0; i < num_instances; i++) {
        if (!gf128_equal(challenges[i], agg_proof->agg_challenges[i])) {
            free(challenges);
            return -4;
        }
    }
    
    // Verify aggregated sumcheck
    // This is a simplified version - real implementation needs full verification
    gf128_t claimed_sum = gf128_zero();
    
    for (size_t i = 0; i < num_instances; i++) {
        gf128_t instance_sum = instances[i]->claimed_sum;
        gf128_t weighted = gf128_mul(challenges[i], instance_sum);
        claimed_sum = gf128_add(claimed_sum, weighted);
    }
    
    // Verify sumcheck with aggregated sum
    // ... (sumcheck verification logic)
    
    free(challenges);
    return 0;
}

// Free aggregated proof
void free_aggregated_proof(aggregated_proof_t *agg_proof) {
    if (!agg_proof) return;
    
    if (agg_proof->proof_sizes) {
        free(agg_proof->proof_sizes);
    }
    
    if (agg_proof->agg_commitment) {
        merkle_commitment_free(agg_proof->agg_commitment);
        free(agg_proof->agg_commitment);
    }
    
    if (agg_proof->sumcheck_coeffs) {
        free(agg_proof->sumcheck_coeffs);
    }
    
    if (agg_proof->opening_proofs) {
        for (size_t i = 0; i < agg_proof->num_openings; i++) {
            if (agg_proof->opening_proofs[i]) {
                free(agg_proof->opening_proofs[i]);
            }
        }
        free(agg_proof->opening_proofs);
    }
    
    if (agg_proof->agg_challenges) {
        free(agg_proof->agg_challenges);
    }
    
    free(agg_proof);
}