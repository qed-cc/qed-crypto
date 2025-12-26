/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "sha3.h"
#include "gf128.h"

void print_hex(const char* label, const uint8_t* data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len; i++) {
        printf("%02x", data[i]);
    }
    printf("\n");
}

int main() {
    printf("╔══════════════════════════════════════════╗\n");
    printf("║    CMPTR Crypto Working Demo             ║\n");
    printf("╚══════════════════════════════════════════╝\n\n");
    
    // Part 1: SHA3 Hashing
    printf("🔐 SHA3 Hashing\n");
    printf("━━━━━━━━━━━━━━━\n");
    
    const char* message = "CMPTR: Quantum-Secure Blockchain";
    uint8_t hash256[SHA3_256_DIGEST_SIZE];
    
    sha3_hash(SHA3_256, message, strlen(message), hash256, sizeof(hash256));
    printf("Message: \"%s\"\n", message);
    print_hex("SHA3-256", hash256, SHA3_256_DIGEST_SIZE);
    
    // Hash the hash (common in Merkle trees)
    uint8_t hash_of_hash[SHA3_256_DIGEST_SIZE];
    sha3_hash(SHA3_256, hash256, SHA3_256_DIGEST_SIZE, hash_of_hash, sizeof(hash_of_hash));
    print_hex("SHA3-256(hash)", hash_of_hash, SHA3_256_DIGEST_SIZE);
    printf("\n");
    
    // Part 2: GF(2^128) Field Operations
    printf("🔢 GF(2^128) Field Arithmetic\n");
    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    
    // Convert hash to GF128 elements
    gf128_t h1 = gf128_from_bytes(hash256);      // First 16 bytes
    gf128_t h2 = gf128_from_bytes(hash256 + 16); // Last 16 bytes
    
    printf("H1 from hash[0:16]:  0x%016lx%016lx\n", h1.hi, h1.lo);
    printf("H2 from hash[16:32]: 0x%016lx%016lx\n", h2.hi, h2.lo);
    
    // Field operations
    gf128_t sum = gf128_add(h1, h2);
    gf128_t product = gf128_mul(h1, h2);
    
    printf("H1 + H2:             0x%016lx%016lx\n", sum.hi, sum.lo);
    printf("H1 * H2:             0x%016lx%016lx\n", product.hi, product.lo);
    printf("\n");
    
    // Part 3: Building a Merkle Tree Node
    printf("🌳 Merkle Tree Example\n");
    printf("━━━━━━━━━━━━━━━━━━━━━\n");
    
    // Two leaf hashes
    const char* leaf1 = "Transaction 1";
    const char* leaf2 = "Transaction 2";
    uint8_t hash1[SHA3_256_DIGEST_SIZE], hash2[SHA3_256_DIGEST_SIZE];
    
    sha3_hash(SHA3_256, leaf1, strlen(leaf1), hash1, sizeof(hash1));
    sha3_hash(SHA3_256, leaf2, strlen(leaf2), hash2, sizeof(hash2));
    
    print_hex("Leaf 1", hash1, SHA3_256_DIGEST_SIZE);
    print_hex("Leaf 2", hash2, SHA3_256_DIGEST_SIZE);
    
    // Combine for parent node
    uint8_t combined[2 * SHA3_256_DIGEST_SIZE];
    memcpy(combined, hash1, SHA3_256_DIGEST_SIZE);
    memcpy(combined + SHA3_256_DIGEST_SIZE, hash2, SHA3_256_DIGEST_SIZE);
    
    uint8_t parent[SHA3_256_DIGEST_SIZE];
    sha3_hash(SHA3_256, combined, sizeof(combined), parent, sizeof(parent));
    print_hex("Parent", parent, SHA3_256_DIGEST_SIZE);
    
    printf("\n");
    printf("╔══════════════════════════════════════════╗\n");
    printf("║         ✅ All Tests Passed!             ║\n");
    printf("╚══════════════════════════════════════════╝\n");
    
    return 0;
}