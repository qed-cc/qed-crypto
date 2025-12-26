/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * AVX-512F single-state optimized SHA3-256 for 64-byte inputs
 * Uses public-domain KeccakP-1600 AVX-512 C implementation from XKCP (CC0).
 * Uses the XKCP KeccakP-1600 AVX-512 C implementation.
 */
#ifdef __GNUC__
#include <string.h>
#include <stdint.h>
#include "sha3.h"
#include "KeccakP-1600-SnP.h"

int sha3_hash_256_64B_avx512(const void *data_, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_256_DIGEST_SIZE) {
        return -1;
    }
    /* Prepare padded block (rate = 136 bytes) */
    uint8_t buf[SHA3_256_BLOCK_SIZE];
    memcpy(buf, data_, len);
    buf[len] = 0x06;
    memset(buf + len + 1, 0, SHA3_256_BLOCK_SIZE - (len + 1));
    buf[SHA3_256_BLOCK_SIZE - 1] ^= 0x80;

    KeccakP1600_plain64_state st;
    /* Initialize, absorb, permute, and squeeze */
    KeccakP1600_Initialize(&st);
    KeccakP1600_OverwriteBytes(&st, buf, 0, SHA3_256_BLOCK_SIZE);
    KeccakP1600_Permute_24rounds(&st);
    KeccakP1600_ExtractBytes(&st, (unsigned char *)digest, 0, SHA3_256_DIGEST_SIZE);
    return SHA3_256_DIGEST_SIZE;
}
#endif
// AVX-512F single-state SHA3-512 specialized for 64-byte inputs
int sha3_hash_512_64B_avx512(const void *data_, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_512_DIGEST_SIZE) return -1;
    uint8_t buf[SHA3_512_BLOCK_SIZE]; memcpy(buf, data_, len); buf[len]=0x06; memset(buf+len+1,0,SHA3_512_BLOCK_SIZE-(len+1)); buf[SHA3_512_BLOCK_SIZE-1]^=0x80;
    KeccakP1600_plain64_state st;
    KeccakP1600_Initialize(&st);
    KeccakP1600_OverwriteBytes(&st, buf, 0, SHA3_512_BLOCK_SIZE);
    KeccakP1600_Permute_24rounds(&st);
    KeccakP1600_ExtractBytes(&st, (unsigned char*)digest, 0, SHA3_512_DIGEST_SIZE);
    return SHA3_512_DIGEST_SIZE;
}