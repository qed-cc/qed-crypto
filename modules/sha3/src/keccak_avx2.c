/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * AVX2-optimized 4-way Keccak-f[1600] permutation
 * Processes four independent states in parallel using AVX2 256-bit vectors.
 */
#ifdef __GNUC__
#include <immintrin.h>
#include <stdint.h>
#include "sha3.h"

/* Round constants for Keccak-f[1600] */
static const uint64_t keccak_rc_avx2[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};

/* 256-bit left rotate by n bits (per 64-bit lane) */
static inline __m256i rotl256(__m256i v, int n) {
    return _mm256_or_si256(_mm256_slli_epi64(v, n), _mm256_srli_epi64(v, 64 - n));
}

/* 4-way Keccak-f[1600] permutation using AVX2 */
__attribute__((target("avx2")))
void keccak_permutation4_avx2(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3) {
    __m256i A[25];
    /* Pack 4 states into 25 vectors */
    for (int i = 0; i < 25; i++) {
        A[i] = _mm256_set_epi64x(s3[i], s2[i], s1[i], s0[i]);
    }
    /* Rounds */
    for (int round = 0; round < 24; round++) {
        __m256i C[5], D[5], T0, T1;
        /* Theta */
        C[0] = _mm256_xor_si256(_mm256_xor_si256(A[0], A[5]), _mm256_xor_si256(A[10], _mm256_xor_si256(A[15], A[20])));
        C[1] = _mm256_xor_si256(_mm256_xor_si256(A[1], A[6]), _mm256_xor_si256(A[11], _mm256_xor_si256(A[16], A[21])));
        C[2] = _mm256_xor_si256(_mm256_xor_si256(A[2], A[7]), _mm256_xor_si256(A[12], _mm256_xor_si256(A[17], A[22])));
        C[3] = _mm256_xor_si256(_mm256_xor_si256(A[3], A[8]), _mm256_xor_si256(A[13], _mm256_xor_si256(A[18], A[23])));
        C[4] = _mm256_xor_si256(_mm256_xor_si256(A[4], A[9]), _mm256_xor_si256(A[14], _mm256_xor_si256(A[19], A[24])));
        D[0] = _mm256_xor_si256(C[4], rotl256(C[1], 1));
        D[1] = _mm256_xor_si256(C[0], rotl256(C[2], 1));
        D[2] = _mm256_xor_si256(C[1], rotl256(C[3], 1));
        D[3] = _mm256_xor_si256(C[2], rotl256(C[4], 1));
        D[4] = _mm256_xor_si256(C[3], rotl256(C[0], 1));
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++) {
                A[x + 5*y] = _mm256_xor_si256(A[x + 5*y], D[x]);
            }
        }
        /* Rho and Pi */
        T0 = A[1]; T1 = A[10]; A[10] = rotl256(T0, 1); T0 = A[7];  A[7]  = rotl256(T1, 3);
        T1 = A[11]; A[11] = rotl256(T0, 6); T0 = A[17]; A[17] = rotl256(T1, 10);
        T1 = A[18]; A[18] = rotl256(T0, 15); T0 = A[3];  A[3]  = rotl256(T1, 21);
        T1 = A[5];  A[5]  = rotl256(T0, 28); T0 = A[16]; A[16] = rotl256(T1, 36);
        T1 = A[8];  A[8]  = rotl256(T0, 45); T0 = A[21]; A[21] = rotl256(T1, 55);
        T1 = A[24]; A[24] = rotl256(T0, 2);  T0 = A[4];  A[4]  = rotl256(T1, 14);
        T1 = A[15]; A[15] = rotl256(T0, 27); T0 = A[23]; A[23] = rotl256(T1, 41);
        T1 = A[19]; A[19] = rotl256(T0, 56); T0 = A[13]; A[13] = rotl256(T1, 8);
        T1 = A[12]; A[12] = rotl256(T0, 25); T0 = A[2];  A[2]  = rotl256(T1, 43);
        T1 = A[20]; A[20] = rotl256(T0, 62); T0 = A[14]; A[14] = rotl256(T1, 18);
        T1 = A[22]; A[22] = rotl256(T0, 39); T0 = A[9];  A[9]  = rotl256(T1, 61);
        T1 = A[6];  A[6]  = rotl256(T0, 20); A[1] = rotl256(T1, 44);
        /* Chi */
        for (int j = 0; j < 25; j += 5) {
            __m256i a0 = A[j+0], a1 = A[j+1], a2 = A[j+2], a3 = A[j+3], a4 = A[j+4];
            A[j+0] = _mm256_xor_si256(a0, _mm256_andnot_si256(a1, a2));
            A[j+1] = _mm256_xor_si256(a1, _mm256_andnot_si256(a2, a3));
            A[j+2] = _mm256_xor_si256(a2, _mm256_andnot_si256(a3, a4));
            A[j+3] = _mm256_xor_si256(a3, _mm256_andnot_si256(a4, a0));
            A[j+4] = _mm256_xor_si256(a4, _mm256_andnot_si256(a0, a1));
        }
        /* Iota */
        A[0] = _mm256_xor_si256(A[0], _mm256_set1_epi64x(keccak_rc_avx2[round]));
    }
    /* Unpack results back to states */
    uint64_t tmp[4] __attribute__((aligned(32)));
    for (int i = 0; i < 25; i++) {
        _mm256_store_si256((__m256i*)tmp, A[i]);
        s0[i] = tmp[0]; s1[i] = tmp[1]; s2[i] = tmp[2]; s3[i] = tmp[3];
    }
}
#endif