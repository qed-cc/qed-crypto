/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * AVX-512F 8-way SHA3-256 specialized for 64-byte inputs
 * Wrapper for XKCP KeccakP-1600-times8 SIMD512 code (public domain CC0).
 * Uses KeccakP-1600-times8 SIMD512 kernel for 8× parallelism.
 */
#ifdef __GNUC__
#include <string.h>
#include <stdint.h>
#include "sha3.h"
#include "KeccakP-1600-times8-SnP.h"

/* KeccakP-1600×8 API from XKCP */
extern void KeccakP1600times8_OverwriteBytes(KeccakP1600times8_SIMD512_states *states, unsigned int instanceIndex, const unsigned char *data, unsigned int offset, unsigned int length);
extern void KeccakP1600times8_PermuteAll_24rounds(KeccakP1600times8_SIMD512_states *states);
extern void KeccakP1600times8_ExtractBytes(const KeccakP1600times8_SIMD512_states *states, unsigned int instanceIndex, unsigned char *data, unsigned int offset, unsigned int length);

int sha3_hash_256_64B_avx512_times8(const void *data_, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_256_DIGEST_SIZE) {
        return -1;
    }
    /* Prepare padded block (rate = 136 bytes) */
    uint8_t buf[SHA3_256_BLOCK_SIZE];
    memcpy(buf, data_, len);
    buf[len] = 0x06;
    memset(buf + len + 1, 0, SHA3_256_BLOCK_SIZE - (len + 1));
    buf[SHA3_256_BLOCK_SIZE - 1] ^= 0x80;

    KeccakP1600times8_SIMD512_states states;
    /* Initialize and absorb into each of the 8 lanes */
    for (unsigned int i = 0; i < 8; i++) {
        KeccakP1600times8_OverwriteBytes(&states, i, buf, 0, SHA3_256_BLOCK_SIZE);
    }
    /* Apply the full 24-round permutation to all 8 states */
    KeccakP1600times8_PermuteAll_24rounds(&states);
    /* Extract the first 32 bytes (SHA3-256 digest) of lane 0 */
    KeccakP1600times8_ExtractBytes(&states, 0, (unsigned char *)digest, 0, SHA3_256_DIGEST_SIZE);
    return SHA3_256_DIGEST_SIZE;
}
#endif
// AVX-512F 8-way SHA3-512 for 64-byte inputs
int sha3_hash_512_64B_avx512_times8(const void *data_, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_512_DIGEST_SIZE) return -1;
    uint8_t buf[SHA3_512_BLOCK_SIZE]; memcpy(buf, data_, len); buf[len] = 0x06;
    memset(buf + len + 1, 0, SHA3_512_BLOCK_SIZE - (len + 1)); buf[SHA3_512_BLOCK_SIZE-1] ^= 0x80;
    KeccakP1600times8_SIMD512_states st;
    for (unsigned int i=0; i<8; i++) KeccakP1600times8_OverwriteBytes(&st, i, buf, 0, SHA3_512_BLOCK_SIZE);
    KeccakP1600times8_PermuteAll_24rounds(&st);
    KeccakP1600times8_ExtractBytes(&st, 0, (unsigned char*)digest, 0, SHA3_512_DIGEST_SIZE);
    return SHA3_512_DIGEST_SIZE;
}