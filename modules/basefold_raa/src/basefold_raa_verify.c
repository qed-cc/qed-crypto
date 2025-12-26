/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "basefold_raa.h"
#include "basefold_raa_internal.h"
#include "sha3.h"
#include "transcript.h"
#include "secure_random.h"
#include "secure_compare.h"  /* For constant-time comparisons */
#include "merkle/verify.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "logger.h"
#include "input_validation.h"

/**
 * @brief Verify BaseFold RAA proof
 * 
 * Verification process:
 * 1. Replay sumcheck protocol
 * 2. Verify RAA codeword consistency
 * 3. Check opening proofs
 */
int basefold_raa_verify(const basefold_raa_proof_t* proof,
                       const basefold_raa_config_t* config) {
    
    if (!proof || !config) {
        return -1;
    }
    
    // Basic sanity checks
    if (proof->num_sumcheck_rounds != config->num_variables) {
        printf("[Verify] Error: Sumcheck rounds mismatch\n");
        return -2;
    }
    
    // Validate number of queries
    if (proof->num_queries == 0 || proof->num_queries > 1000) {
        printf("[Verify] Error: Invalid number of queries: %zu\n", proof->num_queries);
        return -3;
    }
    
    // Validate proof buffer sizes
    if (validate_buffer(proof->sumcheck_responses, 
                       proof->num_sumcheck_rounds * sizeof(gf128_t) * 3,
                       MAX_INPUT_SIZE) != VALIDATION_SUCCESS) {
        printf("[Verify] Error: Invalid sumcheck proof buffer\n");
        return -4;
    }
    
    // Initialize transcript with deterministic seed based on public inputs
    // This ensures prover and verifier start with same state
    fiat_shamir_t transcript;
    uint8_t seed[16] = {0};
    memcpy(seed, &config->num_variables, sizeof(size_t));
    memcpy(seed + sizeof(size_t), &config->security_level, sizeof(uint32_t));
    fs_init_with_domain(&transcript, seed, "BASEFOLD_RAA_V1");
    
    printf("[BaseFold RAA] Starting verification...\n");
    
    // Step 1: Replay sumcheck protocol
    printf("  Step 1: Verifying sumcheck rounds...\n");
    
    gf128_t expected_sum = gf128_zero();  // Should match claimed evaluation
    
    for (size_t round = 0; round < config->num_variables; round++) {
        // Get polynomial values for this round
        gf128_t g0 = proof->sumcheck_responses[round * 3];
        gf128_t g1 = proof->sumcheck_responses[round * 3 + 1];
        gf128_t g2 = proof->sumcheck_responses[round * 3 + 2];
        
        // Verify polynomial consistency: g(0) + g(1) should equal previous sum
        if (round == 0) {
            // First round: sum should be the claimed sum over hypercube
            expected_sum = gf128_add(g0, g1);
        } else {
            // Check consistency with previous round
            gf128_t sum_check = gf128_add(g0, g1);
            if (!gf128_eq(sum_check, expected_sum)) {
                printf("[Verify] Error: Sumcheck round %zu inconsistent\n", round);
                return -5;
            }
        }
        
        // Verify commitment
        sha3_ctx commit_ctx;
        sha3_init(&commit_ctx, SHA3_256);
        sha3_update(&commit_ctx, (uint8_t*)&g0, sizeof(gf128_t));
        sha3_update(&commit_ctx, (uint8_t*)&g1, sizeof(gf128_t));
        
        uint8_t expected_commitment[32];
        sha3_final(&commit_ctx, expected_commitment, 32);
        
        /* SECURITY FIX: Use constant-time comparison to prevent timing attacks */
        if (secure_cmp32(expected_commitment, proof->sumcheck_commitments + round * 32) != 0) {
            printf("[Verify] Error: Sumcheck commitment %zu mismatch\n", round);
            return -6;
        }
        
        // Add to transcript and get challenge
        fs_absorb(&transcript, proof->sumcheck_commitments + round * 32, 32);
        
        uint8_t challenge_bytes[16];
        uint8_t challenge_full[32];
        fs_challenge(&transcript, challenge_full);
        memcpy(challenge_bytes, challenge_full, 16);
        gf128_t r_i = gf128_from_bytes(challenge_bytes);
        
        // Update expected sum for next round
        // Evaluate g_i at r_i
        gf128_t one_minus_r = gf128_add(gf128_one(), r_i);
        expected_sum = gf128_add(
            gf128_mul(one_minus_r, g0),
            gf128_mul(r_i, g1)
        );
    }
    
    // After all rounds, expected_sum should equal the claimed evaluation
    if (!gf128_eq(expected_sum, proof->claimed_eval)) {
        printf("[Verify] Error: Final sumcheck value mismatch\n");
        return -7;
    }
    
    // Step 2: Verify RAA commitment
    printf("  Step 2: Verifying RAA commitment...\n");
    
    // Add RAA root to transcript
    fs_absorb(&transcript, proof->raa_root, 32);
    
    // Initialize RAA parameters with fixed seed for consistent permutations
    basefold_raa_params_t raa_params;
    uint8_t raa_perm_seed[32] = {0};
    memcpy(raa_perm_seed, BASEFOLD_RAA_PERMUTATION_SEED, 32);
    
    // Generate query seed from transcript (for query indices, not permutations)
    uint8_t query_seed[32];
    fs_challenge(&transcript, query_seed);
    
    size_t poly_degree = proof->witness_size - 1;
    int ret = basefold_raa_init_params(&raa_params, poly_degree + 1,
                                       BASEFOLD_RAA_REPETITION_FACTOR, raa_perm_seed);
    if (ret != 0) {
        return -8;
    }
    
    // Step 3: Verify query responses and Merkle paths
    printf("  Step 3: Verifying %zu query responses with Merkle paths...\n", proof->num_queries);
    
    // Calculate expected Merkle path size
    size_t num_leaves = (raa_params.codeword_len + 7) / 8;  // 8 elements per leaf
    size_t tree_depth = 0;
    size_t temp = num_leaves;
    while (temp > 1) {
        tree_depth++;
        temp = (temp + 3) / 4;  // 4-ary tree
    }
    
    // Generate expected query positions and verify Merkle paths
    for (size_t i = 0; i < proof->num_queries; i++) {
        uint8_t idx_bytes[8];
        uint8_t idx_full[32];
        fs_challenge(&transcript, idx_full);
        memcpy(idx_bytes, idx_full, 8);
        
        uint64_t expected_idx = 0;
        for (int j = 0; j < 8; j++) {
            expected_idx = (expected_idx << 8) | idx_bytes[j];
        }
        expected_idx = expected_idx % raa_params.codeword_len;
        
        if (proof->query_indices[i] != expected_idx) {
            printf("[Verify] Error: Query index %zu mismatch\n", i);
            basefold_raa_free_params(&raa_params);
            return -9;
        }
        
        // Verify Merkle path
        if (!proof->merkle_paths || !proof->merkle_paths[i]) {
            printf("[Verify] Error: Missing Merkle path for query %zu\n", i);
            basefold_raa_free_params(&raa_params);
            return -11;
        }
        
        // Check if we have complete leaf values
        if (!proof->query_leaf_values || !proof->query_leaf_values[i]) {
            printf("[Verify] Error: Missing leaf values for query %zu\n", i);
            basefold_raa_free_params(&raa_params);
            return -13;
        }
        
        // Get the leaf index
        size_t leaf_idx = proof->query_indices[i] / 8;  // 8 elements per leaf
        
        // Verify the Merkle path using the complete leaf values
        int path_result = merkle_verify_leaf_group(
            proof->raa_root,
            tree_depth,
            leaf_idx,
            proof->query_leaf_values[i],
            proof->merkle_paths[i]
        );
        
        if (path_result != 0) {
            printf("[Verify] Error: Invalid Merkle path for query %zu (leaf %zu)\n", i, leaf_idx);
            basefold_raa_free_params(&raa_params);
            return -12;
        }
    }
    
    // Verify RAA codeword consistency at query positions
    ret = basefold_raa_verify_consistency(proof->query_values, &raa_params,
                                         proof->query_indices, proof->num_queries);
    if (ret != 0) {
        printf("[Verify] Error: RAA consistency check failed\n");
        basefold_raa_free_params(&raa_params);
        return -10;
    }
    
    // Verify final proof tag
    uint8_t expected_tag[32];
    fs_challenge(&transcript, expected_tag);
    
    if (memcmp(expected_tag, proof->proof_tag, 32) != 0) {
        printf("[Verify] Error: Proof tag mismatch\n");
        basefold_raa_free_params(&raa_params);
        return -11;
    }
    
    printf("  ✓ Verification successful!\n");
    
    // Cleanup
    basefold_raa_free_params(&raa_params);
    
    return 0;
}