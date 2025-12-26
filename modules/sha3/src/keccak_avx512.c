/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * AVX-512F-optimized 8-way Keccak-f[1600] permutation
 * Processes eight independent states in parallel using AVX-512 512-bit vectors.
 */
#ifdef __GNUC__
#include <immintrin.h>
#include <stdint.h>
#include "sha3.h"

/* Round constants (same as scalar/AVX2) */
static const uint64_t keccak_rc_avx2[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};

/* 512-bit left rotate by n bits (per 64-bit lane) */
static inline __m512i rotl512(__m512i v, int n) {
    return _mm512_or_si512(_mm512_slli_epi64(v, n), _mm512_srli_epi64(v, 64 - n));
}

/* 8-way AVX-512F Keccak-f[1600] permutation */
__attribute__((target("avx512f")))
void keccak_permutation8_avx512(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3,
                                 uint64_t *s4, uint64_t *s5, uint64_t *s6, uint64_t *s7) {
    __m512i A[25];
    /* Pack 8 states into 25 vectors */
    for (int i = 0; i < 25; i++) {
        A[i] = _mm512_set_epi64(s7[i], s6[i], s5[i], s4[i], s3[i], s2[i], s1[i], s0[i]);
    }
    /* Rounds */
    for (int round = 0; round < 24; round++) {
        __m512i C[5], D[5], T0, T1;
        /* Theta */
        C[0] = _mm512_xor_si512(_mm512_xor_si512(A[0], A[5]), _mm512_xor_si512(A[10], _mm512_xor_si512(A[15], A[20])));
        C[1] = _mm512_xor_si512(_mm512_xor_si512(A[1], A[6]), _mm512_xor_si512(A[11], _mm512_xor_si512(A[16], A[21])));
        C[2] = _mm512_xor_si512(_mm512_xor_si512(A[2], A[7]), _mm512_xor_si512(A[12], _mm512_xor_si512(A[17], A[22])));
        C[3] = _mm512_xor_si512(_mm512_xor_si512(A[3], A[8]), _mm512_xor_si512(A[13], _mm512_xor_si512(A[18], A[23])));
        C[4] = _mm512_xor_si512(_mm512_xor_si512(A[4], A[9]), _mm512_xor_si512(A[14], _mm512_xor_si512(A[19], A[24])));
        D[0] = _mm512_xor_si512(C[4], rotl512(C[1], 1));
        D[1] = _mm512_xor_si512(C[0], rotl512(C[2], 1));
        D[2] = _mm512_xor_si512(C[1], rotl512(C[3], 1));
        D[3] = _mm512_xor_si512(C[2], rotl512(C[4], 1));
        D[4] = _mm512_xor_si512(C[3], rotl512(C[0], 1));
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++) {
                A[x + 5*y] = _mm512_xor_si512(A[x + 5*y], D[x]);
            }
        }
        /* Rho and Pi */
        T0 = A[1]; T1 = A[10]; A[10] = rotl512(T0, 1); T0 = A[7];  A[7]  = rotl512(T1, 3);
        T1 = A[11]; A[11] = rotl512(T0, 6); T0 = A[17]; A[17] = rotl512(T1, 10);
        T1 = A[18]; A[18] = rotl512(T0, 15); T0 = A[3];  A[3]  = rotl512(T1, 21);
        T1 = A[5];  A[5]  = rotl512(T0, 28); T0 = A[16]; A[16] = rotl512(T1, 36);
        T1 = A[8];  A[8]  = rotl512(T0, 45); T0 = A[21]; A[21] = rotl512(T1, 55);
        T1 = A[24]; A[24] = rotl512(T0, 2);  T0 = A[4];  A[4]  = rotl512(T1, 14);
        T1 = A[15]; A[15] = rotl512(T0, 27); T0 = A[23]; A[23] = rotl512(T1, 41);
        T1 = A[19]; A[19] = rotl512(T0, 56); T0 = A[13]; A[13] = rotl512(T1, 8);
        T1 = A[12]; A[12] = rotl512(T0, 25); T0 = A[2];  A[2]  = rotl512(T1, 43);
        T1 = A[20]; A[20] = rotl512(T0, 62); T0 = A[14]; A[14] = rotl512(T1, 18);
        T1 = A[22]; A[22] = rotl512(T0, 39); T0 = A[9];  A[9]  = rotl512(T1, 61);
        T1 = A[6];  A[6]  = rotl512(T0, 20); A[1] = rotl512(T1, 44);
        /* Chi */
        for (int j = 0; j < 25; j += 5) {
            __m512i a0 = A[j+0], a1 = A[j+1], a2 = A[j+2], a3 = A[j+3], a4 = A[j+4];
            A[j+0] = _mm512_xor_si512(a0, _mm512_andnot_si512(a1, a2));
            A[j+1] = _mm512_xor_si512(a1, _mm512_andnot_si512(a2, a3));
            A[j+2] = _mm512_xor_si512(a2, _mm512_andnot_si512(a3, a4));
            A[j+3] = _mm512_xor_si512(a3, _mm512_andnot_si512(a4, a0));
            A[j+4] = _mm512_xor_si512(a4, _mm512_andnot_si512(a0, a1));
        }
        /* Iota */
        A[0] = _mm512_xor_si512(A[0], _mm512_set1_epi64(keccak_rc_avx2[round]));
    }
    /* Unpack vectors back to states */
    uint64_t tmp[8];
    for (int i = 0; i < 25; i++) {
        _mm512_store_si512((__m512i*)tmp, A[i]);
        s0[i] = tmp[0]; s1[i] = tmp[1]; s2[i] = tmp[2]; s3[i] = tmp[3];
        s4[i] = tmp[4]; s5[i] = tmp[5]; s6[i] = tmp[6]; s7[i] = tmp[7];
    }
}
#endif