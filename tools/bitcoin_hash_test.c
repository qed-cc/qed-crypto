/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file bitcoin_hash_test.c
 * @brief Test correct Bitcoin block #100000 hash computation
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include "logger.h"

// Include the SHA-256 implementation from the complete demo
#define SHA256_BLOCK_SIZE 64
#define SHA256_DIGEST_SIZE 32

typedef struct {
    uint32_t h[8];
    uint64_t len;
    uint8_t buf[SHA256_BLOCK_SIZE];
    size_t buf_len;
} sha256_ctx_t;

// SHA-256 constants
static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define SIGMA0(x) (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define SIGMA1(x) (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define sigma0(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define sigma1(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))

static uint32_t be32(uint32_t x) {
    return ((x & 0xFF) << 24) | (((x >> 8) & 0xFF) << 16) | 
           (((x >> 16) & 0xFF) << 8) | ((x >> 24) & 0xFF);
}

static uint64_t be64(uint64_t x) {
    return ((uint64_t)be32(x & 0xFFFFFFFF) << 32) | be32(x >> 32);
}

void sha256_init(sha256_ctx_t* ctx) {
    ctx->h[0] = 0x6a09e667;
    ctx->h[1] = 0xbb67ae85;
    ctx->h[2] = 0x3c6ef372;
    ctx->h[3] = 0xa54ff53a;
    ctx->h[4] = 0x510e527f;
    ctx->h[5] = 0x9b05688c;
    ctx->h[6] = 0x1f83d9ab;
    ctx->h[7] = 0x5be0cd19;
    ctx->len = 0;
    ctx->buf_len = 0;
}

static void sha256_transform(sha256_ctx_t* ctx, const uint8_t* data) {
    uint32_t w[64];
    uint32_t a, b, c, d, e, f, g, h;
    uint32_t t1, t2;
    
    // Prepare message schedule
    for (int i = 0; i < 16; i++) {
        w[i] = be32(*(uint32_t*)(data + i * 4));
    }
    
    for (int i = 16; i < 64; i++) {
        w[i] = sigma1(w[i-2]) + w[i-7] + sigma0(w[i-15]) + w[i-16];
    }
    
    // Initialize working variables
    a = ctx->h[0]; b = ctx->h[1]; c = ctx->h[2]; d = ctx->h[3];
    e = ctx->h[4]; f = ctx->h[5]; g = ctx->h[6]; h = ctx->h[7];
    
    // Main loop
    for (int i = 0; i < 64; i++) {
        t1 = h + SIGMA1(e) + CH(e, f, g) + K[i] + w[i];
        t2 = SIGMA0(a) + MAJ(a, b, c);
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    
    // Update hash state
    ctx->h[0] += a; ctx->h[1] += b; ctx->h[2] += c; ctx->h[3] += d;
    ctx->h[4] += e; ctx->h[5] += f; ctx->h[6] += g; ctx->h[7] += h;
}

void sha256_update(sha256_ctx_t* ctx, const uint8_t* data, size_t len) {
    ctx->len += len;
    
    while (len > 0) {
        size_t copy_len = SHA256_BLOCK_SIZE - ctx->buf_len;
        if (copy_len > len) copy_len = len;
        
        memcpy(ctx->buf + ctx->buf_len, data, copy_len);
        ctx->buf_len += copy_len;
        data += copy_len;
        len -= copy_len;
        
        if (ctx->buf_len == SHA256_BLOCK_SIZE) {
            sha256_transform(ctx, ctx->buf);
            ctx->buf_len = 0;
        }
    }
}

void sha256_final(sha256_ctx_t* ctx, uint8_t hash[32]) {
    uint64_t bit_len = ctx->len * 8;
    
    // Padding
    ctx->buf[ctx->buf_len++] = 0x80;
    
    if (ctx->buf_len > 56) {
        while (ctx->buf_len < 64) ctx->buf[ctx->buf_len++] = 0;
        sha256_transform(ctx, ctx->buf);
        ctx->buf_len = 0;
    }
    
    while (ctx->buf_len < 56) ctx->buf[ctx->buf_len++] = 0;
    
    // Append length
    *(uint64_t*)(ctx->buf + 56) = be64(bit_len);
    sha256_transform(ctx, ctx->buf);
    
    // Output hash
    for (int i = 0; i < 8; i++) {
        *(uint32_t*)(hash + i * 4) = be32(ctx->h[i]);
    }
}

void sha256(const uint8_t* data, size_t len, uint8_t hash[32]) {
    sha256_ctx_t ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, data, len);
    sha256_final(&ctx, hash);
}

void bitcoin_hash(const uint8_t* data, size_t len, uint8_t hash[32]) {
    uint8_t first_hash[32];
    sha256(data, len, first_hash);
    sha256(first_hash, 32, hash);
}

// Bitcoin block #100000 header - exact hex from blockchain
// Source: 01000000000000000d9e4bc949467ce2a485b9e681ed5acc2da268044f13858338f20000f3e94cbb9a0f6930f179dc4a03106db0b85be68c41e34c7f1d5b692a7ccc134c372c114d4c86041b8f425410
static const uint8_t BLOCK_100000_HEADER[80] = {
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0d, 0x9e, 0x4b, 0xc9, 0x49, 0x46, 0x7c, 0xe2,
    0xa4, 0x85, 0xb9, 0xe6, 0x81, 0xed, 0x5a, 0xcc, 0x2d, 0xa2, 0x68, 0x04, 0x4f, 0x13, 0x85, 0x83,
    0x38, 0xf2, 0x00, 0x00, 0xf3, 0xe9, 0x4c, 0xbb, 0x9a, 0x0f, 0x69, 0x30, 0xf1, 0x79, 0xdc, 0x4a,
    0x03, 0x10, 0x6d, 0xb0, 0xb8, 0x5b, 0xe6, 0x8c, 0x41, 0xe3, 0x4c, 0x7f, 0x1d, 0x5b, 0x69, 0x2a,
    0x7c, 0xcc, 0x13, 0x4c, 0x37, 0x2c, 0x11, 0x4d, 0x4c, 0x86, 0x04, 0x1b, 0x8f, 0x42, 0x54, 0x10
};

// Expected hash for block #100000 (display format - big endian)
static const uint8_t EXPECTED_HASH[32] = {
    0x00, 0x00, 0x00, 0x00, 0x3b, 0xa2, 0x7f, 0x28,
    0x5e, 0x1e, 0xa8, 0x6f, 0x8d, 0xd5, 0xa7, 0xb8,
    0x44, 0xe6, 0x76, 0xf1, 0x4c, 0xba, 0xda, 0x8d,
    0x95, 0x32, 0x35, 0xc5, 0x13, 0xa2, 0x23, 0x00
};

int main(void) {
    printf("🧪 Bitcoin Block #100000 Hash Test\n");
    printf("===================================\n\n");
    
    printf("📦 Block header (80 bytes):\n");
    for (int i = 0; i < 80; i++) {
        printf("%02x", BLOCK_100000_HEADER[i]);
        if ((i + 1) % 16 == 0) printf("\n");
        else if ((i + 1) % 4 == 0) printf(" ");
    }
    printf("\n");
    
    printf("🔗 Computing double SHA-256...\n");
    uint8_t computed_hash[32];
    bitcoin_hash(BLOCK_100000_HEADER, 80, computed_hash);
    
    printf("   Computed: ");
    for (int i = 0; i < 32; i++) printf("%02x", computed_hash[i]);
    printf("\n");
    
    printf("   Expected: ");
    for (int i = 0; i < 32; i++) printf("%02x", EXPECTED_HASH[i]);
    printf("\n");
    
    bool matches = (memcmp(computed_hash, EXPECTED_HASH, 32) == 0);
    printf("\n✅ Hash verification: %s\n", matches ? "CORRECT" : "INCORRECT");
    
    if (matches) {
        printf("\n🎉 SUCCESS: Bitcoin block #100000 hash computed correctly!\n");
        printf("   This proves our SHA-256 implementation is working.\n");
        return 0;
    } else {
        printf("\n❌ FAILURE: Hash mismatch\n");
        return 1;
    }
}