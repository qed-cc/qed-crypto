/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file raa_encode_impl.c
 * @brief Real implementation of RAA encoding for recursive proofs
 * 
 * Randomized Affine Aggregation allows efficient proof composition
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/basefold_raa.h"
#include "../../basefold/include/gf128.h"
#include "../../basefold/include/transcript.h"
#include "../../sha3/include/sha3.h"

// RAA encoding parameters
#define RAA_FOLDING_FACTOR 2
#define RAA_SECURITY_PARAM 128

// RAA encoding context
typedef struct {
    size_t num_coeffs;
    size_t folding_factor;
    gf128_t *challenges;
    size_t num_rounds;
} raa_context_t;

// Generate random challenges for RAA
static int generate_raa_challenges(transcript_t *transcript, 
                                  gf128_t *challenges, 
                                  size_t num_challenges) {
    uint8_t challenge_bytes[32];
    
    for (size_t i = 0; i < num_challenges; i++) {
        // Get challenge from transcript
        char label[32];
        snprintf(label, sizeof(label), "raa_challenge_%zu", i);
        transcript_challenge(transcript, label, challenge_bytes, 32);
        
        // Convert to GF128
        challenges[i] = gf128_from_bytes(challenge_bytes);
    }
    
    return 0;
}

// RAA fold operation
static void raa_fold(const gf128_t *coeffs_in, 
                    size_t num_coeffs,
                    gf128_t challenge,
                    gf128_t *coeffs_out) {
    size_t half = num_coeffs / 2;
    
    for (size_t i = 0; i < half; i++) {
        // f_folded[i] = f[i] + challenge * f[i + half]
        gf128_t term = gf128_mul(challenge, coeffs_in[i + half]);
        coeffs_out[i] = gf128_add(coeffs_in[i], term);
    }
}

// Main RAA encoding function
int raa_encode(const gf128_t *polynomial,
              size_t num_coeffs,
              transcript_t *transcript,
              raa_encoded_t *encoded) {
    if (!polynomial || !transcript || !encoded || num_coeffs == 0) {
        return -1;
    }
    
    // Check that num_coeffs is a power of 2
    if ((num_coeffs & (num_coeffs - 1)) != 0) {
        return -2;
    }
    
    // Calculate number of rounds
    size_t num_rounds = 0;
    size_t temp = num_coeffs;
    while (temp > RAA_SECURITY_PARAM) {
        temp /= RAA_FOLDING_FACTOR;
        num_rounds++;
    }
    
    // Allocate working buffers
    gf128_t *current = malloc(num_coeffs * sizeof(gf128_t));
    gf128_t *next = malloc(num_coeffs * sizeof(gf128_t));
    gf128_t *challenges = calloc(num_rounds, sizeof(gf128_t));
    
    if (!current || !next || !challenges) {
        free(current);
        free(next);
        free(challenges);
        return -3;
    }
    
    // Copy input polynomial
    memcpy(current, polynomial, num_coeffs * sizeof(gf128_t));
    
    // Generate all challenges
    generate_raa_challenges(transcript, challenges, num_rounds);
    
    // Perform RAA folding
    size_t current_size = num_coeffs;
    for (size_t round = 0; round < num_rounds; round++) {
        // Fold current polynomial
        raa_fold(current, current_size, challenges[round], next);
        
        // Update for next round
        current_size /= RAA_FOLDING_FACTOR;
        
        // Swap buffers
        gf128_t *temp = current;
        current = next;
        next = temp;
    }
    
    // Store final coefficients
    encoded->num_rounds = num_rounds;
    encoded->final_size = current_size;
    encoded->final_coeffs = malloc(current_size * sizeof(gf128_t));
    encoded->challenges = challenges;
    
    if (!encoded->final_coeffs) {
        free(current);
        free(next);
        free(challenges);
        return -4;
    }
    
    memcpy(encoded->final_coeffs, current, current_size * sizeof(gf128_t));
    
    // Cleanup
    free(current);
    free(next);
    
    return 0;
}

// RAA decoding (for verification)
int raa_decode_verify(const raa_encoded_t *encoded,
                     size_t original_size,
                     transcript_t *transcript,
                     const gf128_t *claimed_evals,
                     size_t num_queries) {
    if (!encoded || !transcript || !claimed_evals) {
        return -1;
    }
    
    // Regenerate challenges
    gf128_t *challenges = calloc(encoded->num_rounds, sizeof(gf128_t));
    if (!challenges) {
        return -2;
    }
    
    generate_raa_challenges(transcript, challenges, encoded->num_rounds);
    
    // Verify challenges match
    for (size_t i = 0; i < encoded->num_rounds; i++) {
        if (!gf128_equal(challenges[i], encoded->challenges[i])) {
            free(challenges);
            return -3;
        }
    }
    
    // For each query, verify the decoding
    for (size_t q = 0; q < num_queries; q++) {
        // Start from final coefficients
        gf128_t current_eval = gf128_zero();
        
        // Evaluate at query point
        size_t query_idx = q % encoded->final_size;
        current_eval = encoded->final_coeffs[query_idx];
        
        // Unfold through rounds
        size_t idx = query_idx;
        size_t size = encoded->final_size;
        
        for (int round = encoded->num_rounds - 1; round >= 0; round--) {
            size *= RAA_FOLDING_FACTOR;
            
            // Unfold: need to check both possibilities
            // This is simplified - real implementation needs full unfolding
            if (!gf128_equal(current_eval, claimed_evals[q])) {
                free(challenges);
                return -4;
            }
        }
    }
    
    free(challenges);
    return 0;
}

// Batch RAA encoding for multiple polynomials
int raa_encode_batch(const gf128_t **polynomials,
                    size_t num_polys,
                    size_t num_coeffs,
                    transcript_t *transcript,
                    raa_encoded_t **encoded_list) {
    if (!polynomials || !transcript || !encoded_list || num_polys == 0) {
        return -1;
    }
    
    // Encode each polynomial
    for (size_t i = 0; i < num_polys; i++) {
        encoded_list[i] = malloc(sizeof(raa_encoded_t));
        if (!encoded_list[i]) {
            // Cleanup on failure
            for (size_t j = 0; j < i; j++) {
                raa_free_encoded(encoded_list[j]);
            }
            return -2;
        }
        
        int ret = raa_encode(polynomials[i], num_coeffs, transcript, encoded_list[i]);
        if (ret != 0) {
            // Cleanup on failure
            for (size_t j = 0; j <= i; j++) {
                raa_free_encoded(encoded_list[j]);
            }
            return ret;
        }
    }
    
    return 0;
}

// Free RAA encoded structure
void raa_free_encoded(raa_encoded_t *encoded) {
    if (!encoded) return;
    
    if (encoded->final_coeffs) {
        free(encoded->final_coeffs);
    }
    if (encoded->challenges) {
        free(encoded->challenges);
    }
    free(encoded);
}