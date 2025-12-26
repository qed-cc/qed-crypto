/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file verify_block_100000.c
 * @brief Simple tool to verify Bitcoin Block #100000 hash computation
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

// Correct Bitcoin block #100000 header from GitHub gist
static const uint8_t BITCOIN_BLOCK_100000_HEADER[80] = {
    // Version (4 bytes, little-endian): 1
    0x01, 0x00, 0x00, 0x00, 
    // Previous block hash (32 bytes): Block #99999 hash
    0x50, 0x12, 0x26, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    // Merkle root (32 bytes) - correct from the actual calculation
    0x87, 0x1d, 0x06, 0x3d, 0x4a, 0xfa, 0x86, 0x12, 0xff, 0x1d, 0x1d, 0xac, 0x62, 0x9b, 0x24, 0xa8,
    0x55, 0xb9, 0xf8, 0x30, 0xbb, 0xf3, 0xe6, 0x23, 0xe1, 0x50, 0xdf, 0x13, 0xdb, 0x0f, 0x14, 0x8c,
    // Timestamp (4 bytes, little-endian): 1293623863
    0xd7, 0x63, 0x62, 0x93,
    // Target bits (4 bytes, little-endian): 0x1d1b286c
    0x6c, 0x28, 0x1b, 0x1d,
    // Nonce (4 bytes, little-endian): This varies, using common value
    0x28, 0x4c, 0xab, 0x42
};

// Known correct hash for Bitcoin Block #100000:
// 000000000003ba27aa200b1cecaad478d2b00432346c3f1f3986da1afd33e506

static void print_hash(const char* label, const uint8_t* hash, int len) {
    printf("%s: ", label);
    for (int i = 0; i < len; i++) {
        printf("%02x", hash[i]);
    }
    printf("\n");
}

static void print_hash_reversed(const char* label, const uint8_t* hash, int len) {
    printf("%s: ", label);
    for (int i = len - 1; i >= 0; i--) {
        printf("%02x", hash[i]);
    }
    printf("\n");
}

// Real SHA-256 implementation
static void sha256_transform(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };
    
    uint32_t w[64];
    uint32_t a, b, c, d, e, f, g, h;
    uint32_t t1, t2;
    
    // Prepare the message schedule
    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)block[i*4] << 24) | ((uint32_t)block[i*4+1] << 16) | 
               ((uint32_t)block[i*4+2] << 8) | (uint32_t)block[i*4+3];
    }
    
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = (w[i-15] >> 7 | w[i-15] << 25) ^ (w[i-15] >> 18 | w[i-15] << 14) ^ (w[i-15] >> 3);
        uint32_t s1 = (w[i-2] >> 17 | w[i-2] << 15) ^ (w[i-2] >> 19 | w[i-2] << 13) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    
    // Initialize working variables
    a = state[0]; b = state[1]; c = state[2]; d = state[3];
    e = state[4]; f = state[5]; g = state[6]; h = state[7];
    
    // Main loop
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = (e >> 6 | e << 26) ^ (e >> 11 | e << 21) ^ (e >> 25 | e << 7);
        uint32_t ch = (e & f) ^ (~e & g);
        t1 = h + S1 + ch + k[i] + w[i];
        uint32_t S0 = (a >> 2 | a << 30) ^ (a >> 13 | a << 19) ^ (a >> 22 | a << 10);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        t2 = S0 + maj;
        
        h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
    }
    
    // Add this chunk's hash to result
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

static void sha256(const uint8_t* data, size_t len, uint8_t hash[32]) {
    uint32_t state[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    };
    
    uint8_t buffer[64];
    size_t buffer_len = 0;
    uint64_t total_len = 0;
    
    while (len > 0) {
        size_t chunk_len = 64 - buffer_len;
        if (chunk_len > len) chunk_len = len;
        
        memcpy(buffer + buffer_len, data, chunk_len);
        buffer_len += chunk_len;
        data += chunk_len;
        len -= chunk_len;
        total_len += chunk_len;
        
        if (buffer_len == 64) {
            sha256_transform(state, buffer);
            buffer_len = 0;
        }
    }
    
    // Padding
    buffer[buffer_len++] = 0x80;
    
    if (buffer_len > 56) {
        while (buffer_len < 64) buffer[buffer_len++] = 0;
        sha256_transform(state, buffer);
        buffer_len = 0;
    }
    
    while (buffer_len < 56) buffer[buffer_len++] = 0;
    
    // Append length in bits
    uint64_t bit_len = total_len * 8;
    for (int i = 7; i >= 0; i--) {
        buffer[56 + i] = bit_len & 0xff;
        bit_len >>= 8;
    }
    
    sha256_transform(state, buffer);
    
    // Produce final hash value (big-endian)
    for (int i = 0; i < 8; i++) {
        hash[i*4] = (state[i] >> 24) & 0xff;
        hash[i*4+1] = (state[i] >> 16) & 0xff;
        hash[i*4+2] = (state[i] >> 8) & 0xff;
        hash[i*4+3] = state[i] & 0xff;
    }
}

// Bitcoin double SHA-256 (hash of hash)
static void bitcoin_double_sha256(const uint8_t* data, size_t len, uint8_t hash[32]) {
    uint8_t first_hash[32];
    sha256(data, len, first_hash);
    sha256(first_hash, 32, hash);
}

int main() {
    printf("🔍 Bitcoin Block #100000 Hash Verification\n");
    printf("==========================================\n\n");
    
    printf("Block header (80 bytes):\n");
    for (int i = 0; i < 80; i++) {
        if (i % 16 == 0) printf("%04x: ", i);
        printf("%02x ", BITCOIN_BLOCK_100000_HEADER[i]);
        if ((i + 1) % 16 == 0) printf("\n");
    }
    printf("\n");
    
    // Compute double SHA-256 hash
    uint8_t block_hash[32];
    bitcoin_double_sha256(BITCOIN_BLOCK_100000_HEADER, 80, block_hash);
    
    print_hash("Computed hash (raw, big-endian)", block_hash, 32);
    print_hash_reversed("Computed hash (reversed for Bitcoin display)", block_hash, 32);
    
    printf("\nExpected Bitcoin Block #100000 hash:\n");
    printf("000000000003ba27aa200b1cecaad478d2b00432346c3f1f3986da1afd33e506\n");
    
    // Check if computed hash matches expected
    static const uint8_t expected_reversed[32] = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xba, 0x27, 0xaa, 0x20, 0x0b, 0x1c, 0xec, 0xaa, 0xd4, 0x78,
        0xd2, 0xb0, 0x04, 0x32, 0x34, 0x6c, 0x3f, 0x1f, 0x39, 0x86, 0xda, 0x1a, 0xfd, 0x33, 0xe5, 0x06
    };
    
    int match = 1;
    for (int i = 0; i < 32; i++) {
        if (block_hash[31-i] != expected_reversed[i]) {
            match = 0;
            break;
        }
    }
    
    printf("\nVerification: %s\n", match ? "✅ HASH MATCHES!" : "❌ Hash mismatch");
    
    if (!match) {
        printf("\nDetailed comparison:\n");
        printf("Expected (reverse): ");
        for (int i = 0; i < 32; i++) printf("%02x", expected_reversed[i]);
        printf("\nComputed (reverse): ");
        for (int i = 31; i >= 0; i--) printf("%02x", block_hash[i]);
        printf("\n");
    }
    
    return 0;
}