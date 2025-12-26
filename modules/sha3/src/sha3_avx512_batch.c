/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file sha3_avx512_batch.c
 * @brief AVX-512 implementation computing 8 SHA3-256 hashes in parallel
 * 
 * Key optimization for sub-second recursive proofs
 */

#include <immintrin.h>
#include <string.h>
#include <stdint.h>

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

// Rotation offsets
static const unsigned r[24] = {
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
    27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44
};

// Process 8 Keccak states in parallel
static void keccak_f1600_x8_avx512(__m512i state[25]) {
    __m512i C[5], D[5], B[25];
    
    for (int round = 0; round < 24; round++) {
        // Theta step
        C[0] = _mm512_xor_epi64(state[0], state[5]);
        C[0] = _mm512_xor_epi64(C[0], state[10]);
        C[0] = _mm512_xor_epi64(C[0], state[15]);
        C[0] = _mm512_xor_epi64(C[0], state[20]);
        
        C[1] = _mm512_xor_epi64(state[1], state[6]);
        C[1] = _mm512_xor_epi64(C[1], state[11]);
        C[1] = _mm512_xor_epi64(C[1], state[16]);
        C[1] = _mm512_xor_epi64(C[1], state[21]);
        
        C[2] = _mm512_xor_epi64(state[2], state[7]);
        C[2] = _mm512_xor_epi64(C[2], state[12]);
        C[2] = _mm512_xor_epi64(C[2], state[17]);
        C[2] = _mm512_xor_epi64(C[2], state[22]);
        
        C[3] = _mm512_xor_epi64(state[3], state[8]);
        C[3] = _mm512_xor_epi64(C[3], state[13]);
        C[3] = _mm512_xor_epi64(C[3], state[18]);
        C[3] = _mm512_xor_epi64(C[3], state[23]);
        
        C[4] = _mm512_xor_epi64(state[4], state[9]);
        C[4] = _mm512_xor_epi64(C[4], state[14]);
        C[4] = _mm512_xor_epi64(C[4], state[19]);
        C[4] = _mm512_xor_epi64(C[4], state[24]);
        
        // D = C<<<1 xor C
        D[0] = _mm512_xor_epi64(C[4], _mm512_rol_epi64(C[1], 1));
        D[1] = _mm512_xor_epi64(C[0], _mm512_rol_epi64(C[2], 1));
        D[2] = _mm512_xor_epi64(C[1], _mm512_rol_epi64(C[3], 1));
        D[3] = _mm512_xor_epi64(C[2], _mm512_rol_epi64(C[4], 1));
        D[4] = _mm512_xor_epi64(C[3], _mm512_rol_epi64(C[0], 1));
        
        // XOR with D
        for (int i = 0; i < 25; i++) {
            state[i] = _mm512_xor_epi64(state[i], D[i % 5]);
        }
        
        // Rho and Pi steps
        __m512i current = state[1];
        for (int i = 0; i < 24; i++) {
            int j = (2 * i + 3 * (i / 5)) % 5;
            int k = i / 5;
            B[j * 5 + k] = _mm512_rol_epi64(current, r[i]);
            current = state[j * 5 + k];
        }
        B[0] = state[0];
        
        // Chi step
        for (int j = 0; j < 5; j++) {
            __m512i T[5];
            for (int i = 0; i < 5; i++) {
                T[i] = B[j * 5 + i];
            }
            for (int i = 0; i < 5; i++) {
                state[j * 5 + i] = _mm512_xor_epi64(T[i], 
                    _mm512_andnot_epi64(T[(i + 1) % 5], T[(i + 2) % 5]));
            }
        }
        
        // Iota step
        state[0] = _mm512_xor_epi64(state[0], _mm512_set1_epi64(RC[round]));
    }
}

// SHA3-256 for 8 messages in parallel
void sha3_256_x8_avx512(const uint8_t *in[8], size_t inlen, uint8_t out[8][32]) {
    __m512i state[25];
    
    // Initialize states to zero
    for (int i = 0; i < 25; i++) {
        state[i] = _mm512_setzero_si512();
    }
    
    // Absorb phase - simplified for fixed-size inputs
    // In practice, this would handle arbitrary lengths
    for (size_t block = 0; block < inlen; block += 136) {
        // Load 8 blocks of data
        for (int lane = 0; lane < 17; lane++) {  // 136 bytes = 17 lanes
            uint64_t data[8];
            for (int msg = 0; msg < 8; msg++) {
                memcpy(&data[msg], &in[msg][block + lane * 8], 8);
            }
            __m512i lane_data = _mm512_loadu_si512(data);
            state[lane] = _mm512_xor_epi64(state[lane], lane_data);
        }
        
        // Apply Keccak permutation
        keccak_f1600_x8_avx512(state);
    }
    
    // Padding and final block
    uint64_t padding[8] = {0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06};
    state[17] = _mm512_xor_epi64(state[17], _mm512_loadu_si512(padding));
    
    uint64_t final_bit[8] = {
        0x8000000000000000ULL, 0x8000000000000000ULL,
        0x8000000000000000ULL, 0x8000000000000000ULL,
        0x8000000000000000ULL, 0x8000000000000000ULL,
        0x8000000000000000ULL, 0x8000000000000000ULL
    };
    state[16] = _mm512_xor_epi64(state[16], _mm512_loadu_si512(final_bit));
    
    // Final permutation
    keccak_f1600_x8_avx512(state);
    
    // Squeeze phase - extract 32 bytes from each
    for (int msg = 0; msg < 8; msg++) {
        uint64_t output[4];
        for (int i = 0; i < 4; i++) {
            _mm512_storeu_si512(output, state[i]);
            memcpy(&out[msg][i * 8], &output[msg], 8);
        }
    }
}

// Batch Merkle verification using vectorized SHA3
typedef struct {
    uint8_t left[32];
    uint8_t right[32];
} merkle_node_t;

// Verify 8 Merkle paths in parallel
void verify_merkle_batch_x8(
    const merkle_node_t paths[8][10],  // 8 paths, depth 10
    const uint8_t leaves[8][32],
    const uint8_t root[32],
    bool results[8]
) {
    uint8_t current[8][32];
    
    // Start with leaves
    for (int i = 0; i < 8; i++) {
        memcpy(current[i], leaves[i], 32);
    }
    
    // Process each level
    for (int level = 0; level < 10; level++) {
        const uint8_t *inputs[8];
        uint8_t concat_data[8][64];
        
        // Prepare inputs for batch hashing
        for (int i = 0; i < 8; i++) {
            if (paths[i][level].left[0] != 0) {
                memcpy(concat_data[i], paths[i][level].left, 32);
                memcpy(concat_data[i] + 32, current[i], 32);
            } else {
                memcpy(concat_data[i], current[i], 32);
                memcpy(concat_data[i] + 32, paths[i][level].right, 32);
            }
            inputs[i] = concat_data[i];
        }
        
        // Compute 8 hashes in parallel
        sha3_256_x8_avx512(inputs, 64, current);
    }
    
    // Check results
    for (int i = 0; i < 8; i++) {
        results[i] = (memcmp(current[i], root, 32) == 0);
    }
}