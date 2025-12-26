/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * AVX2-accelerated single-block SHA3-256 optimized for 64-byte inputs.
 * Replicates the input across four sponge states and uses the 4-way Keccak core.
 */
#ifdef __GNUC__
#include <string.h>
#include <immintrin.h>
#include "sha3.h"

/* Specialized SHA3-256 for 64-byte messages using AVX2 4-way core */
int sha3_hash_256_64B_avx2(const void *data, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_256_DIGEST_SIZE) {
        return -1;
    }
    /* Prepare padded block (rate = 136 bytes) */
    uint8_t buf[SHA3_256_BLOCK_SIZE];
    memcpy(buf, data, len);
    buf[len] = 0x06;
    memset(buf + len + 1, 0, SHA3_256_BLOCK_SIZE - (len + 1));
    buf[SHA3_256_BLOCK_SIZE - 1] ^= 0x80;

    /* Initialize four sponge states (capacity lanes zeroed) */
    uint64_t s0[25] = {0}, s1[25] = {0}, s2[25] = {0}, s3[25] = {0};
    const uint64_t *lanes = (const uint64_t *)buf;
    for (int i = 0; i < (int)(SHA3_256_BLOCK_SIZE / 8); i++) {
        uint64_t v = lanes[i];
        s0[i] = v;
        s1[i] = v;
        s2[i] = v;
        s3[i] = v;
    }
    /* Apply the 4-way permutation */
    extern void keccak_permutation4_avx2(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3);
    keccak_permutation4_avx2(s0, s1, s2, s3);

    /* Extract first 32 bytes from first state */
    uint64_t *out64 = (uint64_t *)digest;
    for (int i = 0; i < (int)(SHA3_256_DIGEST_SIZE / 8); i++) {
        out64[i] = s0[i];
    }
    return SHA3_256_DIGEST_SIZE;
}
#endif
// AVX2 4-way specialized SHA3-512 for 64-byte inputs
int sha3_hash_512_64B_avx2(const void *data, size_t len, void *digest, size_t digest_size) {
    if (len != 64 || digest_size < SHA3_512_DIGEST_SIZE) return -1;
    uint8_t buf[SHA3_512_BLOCK_SIZE]; memcpy(buf, data, len); buf[len]=0x06; memset(buf+len+1,0,SHA3_512_BLOCK_SIZE-(len+1)); buf[SHA3_512_BLOCK_SIZE-1]^=0x80;
    uint64_t s0[25]={0},s1[25]={0},s2[25]={0},s3[25]={0}; const uint64_t *lanes=(const uint64_t*)buf;
    for(int i=0;i< (int)(SHA3_512_BLOCK_SIZE/8);i++){uint64_t v=lanes[i];s0[i]=v;s1[i]=v;s2[i]=v;s3[i]=v;}
    extern void keccak_permutation4_avx2(uint64_t*,uint64_t*,uint64_t*,uint64_t*);
    keccak_permutation4_avx2(s0,s1,s2,s3);
    uint64_t *out=(uint64_t*)digest; for(int i=0;i< (int)(SHA3_512_DIGEST_SIZE/8);i++) out[i]=s0[i];
    return SHA3_512_DIGEST_SIZE;
}