/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/* Keccak permutation implementation with optional AVX2/AVX512 optimizations */
#include "sha3.h"
#include <string.h>
#ifdef __GNUC__
#include <immintrin.h>
/* CPU feature detection */
static inline int cpu_has_avx2(void) {
    return __builtin_cpu_supports("avx2");
}
static inline int cpu_has_avx512f(void) {
    return __builtin_cpu_supports("avx512f");
}
#else
static inline int cpu_has_avx2(void) { return 0; }
static inline int cpu_has_avx512f(void) { return 0; }
#endif

/* Compiler hints for performance */
#if defined(__GNUC__)
# define HOT_FUNC __attribute__((hot))
#else
# define HOT_FUNC
#endif

/* Keccak round constants */
static const uint64_t keccak_rc[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};

/* Rotation offsets: unneeded - constants inlined into code */
/* (tables removed as code is unrolled) */
/* Rotate left (circular left shift), always inline */
static inline __attribute__((always_inline)) uint64_t rotl64(uint64_t x, int n) {
    return (x << n) | (x >> (64 - n));
}

/* Initialize Keccak state */
int keccak_init(uint64_t state[25]) {
    memset(state, 0, 25 * sizeof(uint64_t));
    return 0;
}

/* Keccak-f[1600] permutation */
/* Scalar Keccak-f[1600] permutation */
static HOT_FUNC void keccak_permutation_scalar(uint64_t * __restrict__ state) {
    uint64_t temp, C[5];
    int i, j, round;
    for (round = 0; round < 24; round++) {
        /* Theta */
        for (i = 0; i < 5; i++) {
            C[i] = state[i] ^ state[i + 5] ^ state[i + 10] ^ state[i + 15] ^ state[i + 20];
        }
        /* Theta app */
        temp = C[4] ^ rotl64(C[1], 1);
        state[0] ^= temp; state[5] ^= temp; state[10] ^= temp; state[15] ^= temp; state[20] ^= temp;
        temp = C[0] ^ rotl64(C[2], 1);
        state[1] ^= temp; state[6] ^= temp; state[11] ^= temp; state[16] ^= temp; state[21] ^= temp;
        temp = C[1] ^ rotl64(C[3], 1);
        state[2] ^= temp; state[7] ^= temp; state[12] ^= temp; state[17] ^= temp; state[22] ^= temp;
        temp = C[2] ^ rotl64(C[4], 1);
        state[3] ^= temp; state[8] ^= temp; state[13] ^= temp; state[18] ^= temp; state[23] ^= temp;
        temp = C[3] ^ rotl64(C[0], 1);
        state[4] ^= temp; state[9] ^= temp; state[14] ^= temp; state[19] ^= temp; state[24] ^= temp;
        /* Rho+Pi */
        {
            uint64_t t0 = state[1], t1;
            t1 = state[10]; state[10] = rotl64(t0,  1); t0 = state[7];  state[7]  = rotl64(t1,  3);
            t1 = state[11]; state[11] = rotl64(t0,  6); t0 = state[17]; state[17] = rotl64(t1, 10);
            t1 = state[18]; state[18] = rotl64(t0, 15); t0 = state[3];  state[3]  = rotl64(t1, 21);
            t1 = state[5];  state[5]  = rotl64(t0, 28); t0 = state[16]; state[16] = rotl64(t1, 36);
            t1 = state[8];  state[8]  = rotl64(t0, 45); t0 = state[21]; state[21] = rotl64(t1, 55);
            t1 = state[24]; state[24] = rotl64(t0,  2); t0 = state[4];  state[4]  = rotl64(t1, 14);
            t1 = state[15]; state[15] = rotl64(t0, 27); t0 = state[23]; state[23] = rotl64(t1, 41);
            t1 = state[19]; state[19] = rotl64(t0, 56); t0 = state[13]; state[13] = rotl64(t1,  8);
            t1 = state[12]; state[12] = rotl64(t0, 25); t0 = state[2];  state[2]  = rotl64(t1, 43);
            t1 = state[20]; state[20] = rotl64(t0, 62); t0 = state[14]; state[14] = rotl64(t1, 18);
            t1 = state[22]; state[22] = rotl64(t0, 39); t0 = state[9];  state[9]  = rotl64(t1, 61);
            t1 = state[6];  state[6]  = rotl64(t0, 20); state[1] = rotl64(t1, 44);
        }
        /* Chi */
        for (j = 0; j < 25; j += 5) {
            uint64_t a0 = state[j+0], a1 = state[j+1], a2 = state[j+2], a3 = state[j+3], a4 = state[j+4];
            state[j+0] = a0 ^ ((~a1) & a2);
            state[j+1] = a1 ^ ((~a2) & a3);
            state[j+2] = a2 ^ ((~a3) & a4);
            state[j+3] = a3 ^ ((~a4) & a0);
            state[j+4] = a4 ^ ((~a0) & a1);
        }
        /* Iota */
        state[0] ^= keccak_rc[round];
    }
}
/* AVX2 stub */
/* AVX2 stub: currently calls scalar permutation */
#ifdef __GNUC__
static HOT_FUNC __attribute__((target("avx2"))) void keccak_permutation_avx2(uint64_t * __restrict__ state) {
    keccak_permutation_scalar(state);
}
#endif
/* Dispatcher */
#ifdef __GNUC__
/* AVX-512F 8-way permutation */
extern void keccak_permutation8_avx512(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3,
                                      uint64_t *s4, uint64_t *s5, uint64_t *s6, uint64_t *s7);
#endif
/* Dispatcher for single-state Keccak-f: prefer AVX2, fallback to scalar */
void keccak_permutation(uint64_t * __restrict__ state) {
#ifdef __GNUC__
    if (cpu_has_avx2()) {
        keccak_permutation_avx2(state);
        return;
    }
#endif
    keccak_permutation_scalar(state);
}

/* Absorb data into the Keccak sponge */
HOT_FUNC void keccak_absorb(uint64_t * __restrict__ state, const uint8_t * __restrict__ data, size_t len, size_t rate) {
    size_t i;
    size_t words = rate / 8;
    size_t block_size = rate;
    uint64_t * __restrict__ state_words = state;
    
    /* Process all complete blocks */
    while (len >= block_size) {
        /* XOR input data directly into state lanes, use fast path on aligned data */
        /* Fast path: aligned input */
        if ((((uintptr_t)data) & (sizeof(uint64_t) - 1)) == 0) {
            /* Prefer AVX2 vector XOR on supported hardware */
            if (cpu_has_avx2()) {
                size_t k = 0;
                for (; k + 3 < words; k += 4) {
                    __m256i v_in  = _mm256_load_si256((__m256i const *)(data + k * 8));
                    __m256i v_st  = _mm256_loadu_si256((__m256i const *)(state_words + k));
                    __m256i v_xor = _mm256_xor_si256(v_st, v_in);
                    _mm256_storeu_si256((__m256i *)(state_words + k), v_xor);
                }
                for (; k < words; k++) {
                    state_words[k] ^= ((const uint64_t *)data)[k];
                }
            } else {
                const uint64_t *in = (const uint64_t *)data;
                for (i = 0; i < words; i++) {
                    state_words[i] ^= in[i];
                }
            }
        } else {
            /* Unaligned fallback */
            for (i = 0; i < words; i++) {
                uint64_t lane;
                memcpy(&lane, data + i * sizeof(lane), sizeof(lane));
                state_words[i] ^= lane;
            }
        }
        
        /* Apply the permutation */
        keccak_permutation(state);
        
        data += block_size;
        len -= block_size;
    }
}

/* Squeeze output from the Keccak sponge */
HOT_FUNC void keccak_squeeze(uint64_t * __restrict__ state, uint8_t * __restrict__ output, size_t output_len, size_t rate) {
    size_t i, k;
    size_t block_size = rate;
    size_t blocks = (output_len + block_size - 1) / block_size; /* Ceiling division */
    size_t offset = 0;
    int aligned_out = (((uintptr_t)output) & (sizeof(uint64_t) - 1)) == 0;

    for (i = 0; i < blocks; i++) {
        size_t this_len = (i == blocks - 1) ? (output_len - offset) : block_size;
        size_t full_words = this_len / 8;
        size_t rem_bytes = this_len % 8;

        if (aligned_out) {
            uint64_t *out64 = (uint64_t *)(output + offset);
            /* AVX2 fast store */
            if (cpu_has_avx2()) {
                size_t m = 0;
                for (; m + 3 < full_words; m += 4) {
                    __m256i v = _mm256_loadu_si256((__m256i const *)(state + m));
                    _mm256_store_si256((__m256i *)(out64 + m), v);
                }
                for (; m < full_words; m++) {
                    out64[m] = state[m];
                }
            } else {
                for (k = 0; k < full_words; k++) {
                    out64[k] = state[k];
                }
            }
        } else {
            for (k = 0; k < full_words; k++) {
                uint64_t lane = state[k];
                memcpy(output + offset + k * 8, &lane, 8);
            }
        }
        if (rem_bytes) {
            const uint8_t *state_bytes = (const uint8_t *)state;
            for (k = 0; k < rem_bytes; k++) {
                output[offset + full_words * 8 + k] = state_bytes[full_words * 8 + k];
            }
        }
        offset += this_len;
        if (i < blocks - 1) {
            keccak_permutation(state);
        }
    }
}