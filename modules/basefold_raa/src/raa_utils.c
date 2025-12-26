/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "basefold_raa.h"
#include "sha3.h"
#include <stdlib.h>
#include <string.h>

/**
 * @brief Generate cryptographically secure permutation using Fisher-Yates
 */
static void generate_secure_permutation(size_t* perm, size_t n, 
                                       const uint8_t* seed, 
                                       const char* domain_sep) {
    // Initialize to identity
    for (size_t i = 0; i < n; i++) {
        perm[i] = i;
    }
    
    // Set up PRNG with seed and domain separator
    sha3_ctx prng;
    sha3_init(&prng, SHA3_256);
    sha3_update(&prng, seed, 32);
    sha3_update(&prng, (const uint8_t*)domain_sep, strlen(domain_sep));
    
    // Fisher-Yates shuffle
    for (size_t i = n - 1; i > 0; i--) {
        // Generate random j in [0, i]
        uint8_t rand_bytes[8];
        sha3_ctx temp = prng;
        sha3_update(&temp, (uint8_t*)&i, sizeof(i));
        sha3_final(&temp, rand_bytes, 8);
        
        uint64_t rand_val = 0;
        for (int k = 0; k < 8; k++) {
            rand_val = (rand_val << 8) | rand_bytes[k];
        }
        
        size_t j = rand_val % (i + 1);
        
        // Swap
        size_t tmp = perm[i];
        perm[i] = perm[j];
        perm[j] = tmp;
    }
}

/**
 * @brief Initialize RAA parameters
 */
int basefold_raa_init_params(basefold_raa_params_t* params,
                            size_t message_len,
                            size_t repetition,
                            const uint8_t seed[32]) {
    
    if (!params || message_len == 0 || repetition == 0 || !seed) {
        return -1;
    }
    
    params->message_len = message_len;
    params->repetition = repetition;
    params->codeword_len = message_len * repetition;
    memcpy(params->seed, seed, 32);
    
    // Allocate permutations
    params->perm1 = malloc(params->codeword_len * sizeof(size_t));
    params->perm2 = malloc(params->codeword_len * sizeof(size_t));
    
    if (!params->perm1 || !params->perm2) {
        if (params->perm1) free(params->perm1);
        if (params->perm2) free(params->perm2);
        return -2;
    }
    
    // Generate permutations with different domain separators
    generate_secure_permutation(params->perm1, params->codeword_len, 
                               seed, "BASEFOLD_RAA_PERM1");
    generate_secure_permutation(params->perm2, params->codeword_len, 
                               seed, "BASEFOLD_RAA_PERM2");
    
    return 0;
}

/**
 * @brief Free RAA parameters
 */
void basefold_raa_free_params(basefold_raa_params_t* params) {
    if (params) {
        if (params->perm1) {
            free(params->perm1);
            params->perm1 = NULL;
        }
        if (params->perm2) {
            free(params->perm2);
            params->perm2 = NULL;
        }
    }
}

/**
 * @brief Estimate proof size based on configuration
 */
size_t basefold_raa_proof_size(const basefold_raa_config_t* config) {
    if (!config) return 0;
    
    size_t size = 0;
    
    // Sumcheck commitments (32 bytes per round)
    size += config->num_variables * 32;
    
    // Sumcheck responses (3 field elements per round)
    size += config->num_variables * 3 * sizeof(gf128_t);
    
    // RAA commitment
    size += 32;
    
    // Query responses (100 queries typical)
    size_t num_queries = BASEFOLD_RAA_NUM_QUERIES;
    size += num_queries * sizeof(gf128_t);
    
    // Merkle paths (log(codeword_size) * 32 bytes per query)
    size_t codeword_size = (1ULL << config->num_variables) * BASEFOLD_RAA_REPETITION_FACTOR;
    size_t path_length = 0;
    while (codeword_size > 1) {
        path_length++;
        codeword_size /= 2;
    }
    size += num_queries * path_length * 32;
    
    // Query indices
    size += num_queries * sizeof(size_t);
    
    // Metadata
    size += sizeof(size_t) + 32; // witness_size + proof_tag
    
    return size;
}

/**
 * @brief Free proof structure
 */
void basefold_raa_proof_free(basefold_raa_proof_t* proof) {
    if (!proof) return;
    
    if (proof->sumcheck_commitments) {
        free(proof->sumcheck_commitments);
        proof->sumcheck_commitments = NULL;
    }
    
    if (proof->sumcheck_responses) {
        free(proof->sumcheck_responses);
        proof->sumcheck_responses = NULL;
    }
    
    if (proof->query_values) {
        free(proof->query_values);
        proof->query_values = NULL;
    }
    
    if (proof->merkle_paths) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            if (proof->merkle_paths[i]) {
                free(proof->merkle_paths[i]);
            }
        }
        free(proof->merkle_paths);
        proof->merkle_paths = NULL;
    }
    
    if (proof->query_leaf_values) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            if (proof->query_leaf_values[i]) {
                free(proof->query_leaf_values[i]);
            }
        }
        free(proof->query_leaf_values);
        proof->query_leaf_values = NULL;
    }
    
    if (proof->query_indices) {
        free(proof->query_indices);
        proof->query_indices = NULL;
    }
    
    if (proof->randomizer_coeffs) {
        free(proof->randomizer_coeffs);
        proof->randomizer_coeffs = NULL;
    }
    
    proof->num_queries = 0;
    proof->num_sumcheck_rounds = 0;
    proof->randomizer_degree = 0;
}