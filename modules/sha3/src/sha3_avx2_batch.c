/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file sha3_avx2_batch.c
 * @brief AVX2 implementation computing 4 SHA3-256 hashes in parallel
 * 
 * Real implementation for sub-second recursive proofs
 */

#include <immintrin.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include "../include/sha3.h"
#include "../include/sha3_batch.h"

// Keccak round constants
static const uint64_t RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
    0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
    0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
    0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
    0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};

// Process 4 Keccak states in parallel using AVX2
static void keccak_f1600_x4_avx2(__m256i state[25]) {
    __m256i C[5], D[5], B[25];
    
    for (int round = 0; round < 24; round++) {
        // Theta step
        for (int i = 0; i < 5; i++) {
            C[i] = _mm256_xor_si256(state[i], state[i + 5]);
            C[i] = _mm256_xor_si256(C[i], state[i + 10]);
            C[i] = _mm256_xor_si256(C[i], state[i + 15]);
            C[i] = _mm256_xor_si256(C[i], state[i + 20]);
        }
        
        // D = C<<<1 xor C
        for (int i = 0; i < 5; i++) {
            __m256i rotated = _mm256_or_si256(
                _mm256_slli_epi64(C[(i + 1) % 5], 1),
                _mm256_srli_epi64(C[(i + 1) % 5], 63)
            );
            D[i] = _mm256_xor_si256(C[(i + 4) % 5], rotated);
        }
        
        // Apply D to state
        for (int i = 0; i < 25; i++) {
            state[i] = _mm256_xor_si256(state[i], D[i % 5]);
        }
        
        // Rho and Pi steps combined
        B[0] = state[0];
        int x = 1, y = 0;
        __m256i current = state[1];
        
        for (int t = 0; t < 24; t++) {
            int r = ((t + 1) * (t + 2) / 2) % 64;
            B[y * 5 + x] = _mm256_or_si256(
                _mm256_slli_epi64(current, r),
                _mm256_srli_epi64(current, 64 - r)
            );
            
            int tmp = y;
            y = (2 * x + 3 * y) % 5;
            x = tmp;
            current = state[y * 5 + x];
        }
        
        // Chi step
        for (int j = 0; j < 5; j++) {
            __m256i T[5];
            for (int i = 0; i < 5; i++) {
                T[i] = B[j * 5 + i];
            }
            for (int i = 0; i < 5; i++) {
                __m256i not_next = _mm256_andnot_si256(T[(i + 1) % 5], T[(i + 2) % 5]);
                state[j * 5 + i] = _mm256_xor_si256(T[i], not_next);
            }
        }
        
        // Iota step
        state[0] = _mm256_xor_si256(state[0], _mm256_set1_epi64x(RC[round]));
    }
}

// SHA3-256 for 4 messages in parallel
void sha3_256_x4_avx2(const uint8_t *in[4], size_t inlen[4], uint8_t out[4][32]) {
    __m256i state[25];
    
    // Initialize states to zero
    for (int i = 0; i < 25; i++) {
        state[i] = _mm256_setzero_si256();
    }
    
    // Process each message
    for (int msg = 0; msg < 4; msg++) {
        const uint8_t *data = in[msg];
        size_t len = inlen[msg];
        
        // Absorb full blocks
        while (len >= 136) {
            for (int i = 0; i < 17; i++) {  // 136 bytes = 17 uint64_t
                uint64_t word;
                memcpy(&word, data + i * 8, 8);
                
                // Update the appropriate lane for this message
                uint64_t current[4];
                _mm256_storeu_si256((__m256i*)current, state[i]);
                current[msg] ^= word;
                state[i] = _mm256_loadu_si256((__m256i*)current);
            }
            
            data += 136;
            len -= 136;
            
            // Only permute after all 4 messages have absorbed this block
            if (msg == 3) {
                keccak_f1600_x4_avx2(state);
            }
        }
        
        // Handle padding for each message
        uint8_t pad[136] = {0};
        memcpy(pad, data, len);
        pad[len] = 0x06;  // SHA3 domain separator
        pad[135] = 0x80;  // Final bit
        
        for (int i = 0; i < 17; i++) {
            uint64_t word;
            memcpy(&word, pad + i * 8, 8);
            
            uint64_t current[4];
            _mm256_storeu_si256((__m256i*)current, state[i]);
            current[msg] ^= word;
            state[i] = _mm256_loadu_si256((__m256i*)current);
        }
    }
    
    // Final permutation
    keccak_f1600_x4_avx2(state);
    
    // Extract output for each message
    for (int msg = 0; msg < 4; msg++) {
        for (int i = 0; i < 4; i++) {  // 32 bytes = 4 uint64_t
            uint64_t words[4];
            _mm256_storeu_si256((__m256i*)words, state[i]);
            memcpy(out[msg] + i * 8, &words[msg], 8);
        }
    }
}

// Batch Merkle verification using vectorized SHA3
int verify_merkle_batch_x4_avx2(
    const uint8_t paths[4][10][64],    // 4 paths, depth 10, 64 bytes per node
    const uint8_t leaves[4][32],
    const uint8_t root[32],
    int directions[4][10],             // 0=left, 1=right for each path
    bool results[4]
) {
    uint8_t current[4][32];
    
    // Start with leaves
    for (int i = 0; i < 4; i++) {
        memcpy(current[i], leaves[i], 32);
    }
    
    // Process each level
    for (int level = 0; level < 10; level++) {
        const uint8_t *inputs[4];
        uint8_t concat_data[4][64];
        size_t lengths[4] = {64, 64, 64, 64};
        
        // Prepare inputs for batch hashing
        for (int i = 0; i < 4; i++) {
            if (directions[i][level] == 0) {
                // Current node is left child
                memcpy(concat_data[i], current[i], 32);
                memcpy(concat_data[i] + 32, &paths[i][level][32], 32);
            } else {
                // Current node is right child
                memcpy(concat_data[i], &paths[i][level][0], 32);
                memcpy(concat_data[i] + 32, current[i], 32);
            }
            inputs[i] = concat_data[i];
        }
        
        // Compute 4 hashes in parallel
        sha3_256_x4_avx2(inputs, lengths, current);
    }
    
    // Check results
    int success_count = 0;
    for (int i = 0; i < 4; i++) {
        results[i] = (memcmp(current[i], root, 32) == 0);
        if (results[i]) success_count++;
    }
    
    return success_count;
}