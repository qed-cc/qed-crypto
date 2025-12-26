/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/basefold_raa/include/basefold_raa_internal.h"
#include "../modules/gf128/include/gf128.h"

/**
 * @file minimal_raa_test.c
 * @brief Minimal test to debug RAA consistency
 */

// External functions
extern int basefold_raa_encode(const gf128_t* message,
                              const basefold_raa_params_t* params,
                              gf128_t* codeword);

extern int basefold_raa_verify_consistency(const gf128_t* values,
                                          const basefold_raa_params_t* params,
                                          const size_t* indices,
                                          size_t num_queries);

int main() {
    printf("=== MINIMAL RAA TEST ===\n\n");
    
    // Use exact same parameters as the proof system
    size_t num_vars = 10;
    size_t witness_size = 1ULL << num_vars;
    size_t poly_degree = witness_size - 1;
    
    // Initialize RAA params with the SAME seed
    basefold_raa_params_t params;
    uint8_t seed[32] = {0};
    memcpy(seed, BASEFOLD_RAA_PERMUTATION_SEED, 32);
    
    int ret = basefold_raa_init_params(&params, poly_degree + 1,
                                       BASEFOLD_RAA_REPETITION_FACTOR, seed);
    if (ret != 0) {
        printf("Failed to init params: %d\n", ret);
        return 1;
    }
    
    printf("Parameters:\n");
    printf("  Message length: %zu\n", params.message_len);
    printf("  Codeword length: %zu\n", params.codeword_len);
    printf("  Repetition: %zu\n", params.repetition);
    
    // Create a simple message (simulating univariate coefficients)
    gf128_t* message = calloc(params.message_len, sizeof(gf128_t));
    
    // Set first coefficient to 1, rest to 0 (like a constant polynomial)
    message[0] = gf128_one();
    
    // Encode
    gf128_t* codeword = calloc(params.codeword_len, sizeof(gf128_t));
    ret = basefold_raa_encode(message, &params, codeword);
    if (ret != 0) {
        printf("Encoding failed: %d\n", ret);
        free(message);
        free(codeword);
        basefold_raa_free_params(&params);
        return 1;
    }
    
    printf("\n✓ Encoding successful\n");
    
    // Count zeros in codeword
    int zero_count = 0;
    for (size_t i = 0; i < params.codeword_len; i++) {
        if (gf128_is_zero(codeword[i])) {
            zero_count++;
        }
    }
    printf("Codeword has %d/%zu zeros (%.1f%%)\n", 
           zero_count, params.codeword_len, 
           100.0 * zero_count / params.codeword_len);
    
    // Test consistency with a few random indices
    size_t num_queries = 10;
    size_t* indices = calloc(num_queries, sizeof(size_t));
    gf128_t* values = calloc(num_queries, sizeof(gf128_t));
    
    // Use simple indices for debugging
    for (size_t i = 0; i < num_queries; i++) {
        indices[i] = i * (params.codeword_len / num_queries);
        values[i] = codeword[indices[i]];
        
        printf("\nQuery %zu: idx=%zu, value=", i, indices[i]);
        if (gf128_is_zero(values[i])) {
            printf("0");
        } else {
            uint8_t bytes[16];
            gf128_to_bytes(values[i], bytes);
            printf("%02x%02x...", bytes[0], bytes[1]);
        }
    }
    
    printf("\n\nTesting consistency...\n");
    ret = basefold_raa_verify_consistency(values, &params, indices, num_queries);
    printf("Result: %d\n", ret);
    
    if (ret != 0) {
        printf("\nDEBUGGING: Let's check what the consistency function expects\n");
        
        // The issue might be that we're passing the wrong values
        // Let me check if it's expecting the values in a different order
        printf("\nTrying with all non-zero values...\n");
        for (size_t i = 0; i < num_queries; i++) {
            values[i] = gf128_one();
        }
        ret = basefold_raa_verify_consistency(values, &params, indices, num_queries);
        printf("Result with all ones: %d\n", ret);
    }
    
    // Cleanup
    free(message);
    free(codeword);
    free(indices);
    free(values);
    basefold_raa_free_params(&params);
    
    return 0;
}