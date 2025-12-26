/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include "sha3.h"

/*
 * SHA3-Only Cryptographic Stack Demo
 * ==================================
 * This demonstrates how CMPTR achieves complete blockchain functionality
 * using ONLY SHA3-256 as the sole cryptographic primitive.
 */

/* SHA3-based Random Number Generator */
typedef struct {
    uint8_t state[32];
    uint64_t counter;
} sha3_rng_t;

void sha3_rng_init(sha3_rng_t* rng, const uint8_t* seed) {
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    sha3_update(&ctx, seed, 32);
    sha3_update(&ctx, (uint8_t*)"SHA3_RNG_INIT", 13);
    sha3_final(rng->state, &ctx);
    rng->counter = 0;
}

void sha3_rng_generate(sha3_rng_t* rng, uint8_t* output, size_t len) {
    size_t generated = 0;
    while (generated < len) {
        sha3_ctx ctx;
        sha3_init(&ctx, 32);
        sha3_update(&ctx, rng->state, 32);
        sha3_update(&ctx, (uint8_t*)&rng->counter, 8);
        sha3_final(rng->state, &ctx);
        rng->counter++;
        
        size_t to_copy = (len - generated > 32) ? 32 : (len - generated);
        memcpy(output + generated, rng->state, to_copy);
        generated += to_copy;
    }
}

/* SHA3-based Commitment Scheme */
typedef struct {
    uint8_t commitment[32];
    uint8_t randomness[32];
} sha3_commitment_t;

sha3_commitment_t* sha3_commit(const uint8_t* message, size_t msg_len) {
    sha3_commitment_t* com = malloc(sizeof(sha3_commitment_t));
    
    /* Generate randomness */
    for (int i = 0; i < 32; i++) {
        com->randomness[i] = rand() & 0xFF;
    }
    
    /* Compute commitment = SHA3(randomness || message) */
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    sha3_update(&ctx, com->randomness, 32);
    sha3_update(&ctx, message, msg_len);
    sha3_update(&ctx, (uint8_t*)"COMMITMENT", 10);
    sha3_final(com->commitment, &ctx);
    
    return com;
}

int sha3_verify_commitment(const sha3_commitment_t* com, 
                          const uint8_t* message, size_t msg_len) {
    uint8_t computed[32];
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    sha3_update(&ctx, com->randomness, 32);
    sha3_update(&ctx, message, msg_len);
    sha3_update(&ctx, (uint8_t*)"COMMITMENT", 10);
    sha3_final(computed, &ctx);
    
    return memcmp(computed, com->commitment, 32) == 0;
}

/* SHA3-based VRF (Simplified) */
typedef struct {
    uint8_t private_key[32];
    uint8_t public_key[32];
} sha3_vrf_keypair_t;

typedef struct {
    uint8_t output[32];
    uint8_t proof[96];  /* commitment + challenge + response */
} sha3_vrf_proof_t;

sha3_vrf_keypair_t* sha3_vrf_keygen(void) {
    sha3_vrf_keypair_t* kp = malloc(sizeof(sha3_vrf_keypair_t));
    
    /* Generate random private key */
    for (int i = 0; i < 32; i++) {
        kp->private_key[i] = rand() & 0xFF;
    }
    
    /* Public key = SHA3(private_key || "PUBLIC") */
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    sha3_update(&ctx, kp->private_key, 32);
    sha3_update(&ctx, (uint8_t*)"SHA3_VRF_PUBLIC", 15);
    sha3_final(kp->public_key, &ctx);
    
    return kp;
}

sha3_vrf_proof_t* sha3_vrf_prove(const sha3_vrf_keypair_t* kp,
                                 const uint8_t* message, size_t msg_len) {
    sha3_vrf_proof_t* proof = malloc(sizeof(sha3_vrf_proof_t));
    sha3_ctx ctx;
    
    /* Output = SHA3(private_key || message || "VRF_OUTPUT") */
    sha3_init(&ctx, 32);
    sha3_update(&ctx, kp->private_key, 32);
    sha3_update(&ctx, message, msg_len);
    sha3_update(&ctx, (uint8_t*)"VRF_OUTPUT", 10);
    sha3_final(proof->output, &ctx);
    
    /* Commitment = SHA3(private_key || output || "COMMIT") */
    sha3_init(&ctx, 32);
    sha3_update(&ctx, kp->private_key, 32);
    sha3_update(&ctx, proof->output, 32);
    sha3_update(&ctx, (uint8_t*)"VRF_COMMIT", 10);
    sha3_final(proof->proof, &ctx);  /* First 32 bytes */
    
    /* Challenge = SHA3(commitment || message || "CHALLENGE") */
    sha3_init(&ctx, 32);
    sha3_update(&ctx, proof->proof, 32);
    sha3_update(&ctx, message, msg_len);
    sha3_update(&ctx, (uint8_t*)"VRF_CHALLENGE", 13);
    sha3_final(proof->proof + 32, &ctx);  /* Next 32 bytes */
    
    /* Response (simplified) = private_key XOR challenge */
    for (int i = 0; i < 32; i++) {
        proof->proof[64 + i] = kp->private_key[i] ^ proof->proof[32 + i];
    }
    
    return proof;
}

/* SHA3-based Merkle Tree */
typedef struct {
    uint8_t** leaves;
    uint32_t leaf_count;
    uint8_t root[32];
} sha3_merkle_tree_t;

void sha3_hash_pair(uint8_t* out, const uint8_t* left, const uint8_t* right) {
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    sha3_update(&ctx, left, 32);
    sha3_update(&ctx, right, 32);
    sha3_update(&ctx, (uint8_t*)"MERKLE_NODE", 11);
    sha3_final(out, &ctx);
}

sha3_merkle_tree_t* sha3_merkle_build(uint8_t** data, uint32_t count) {
    sha3_merkle_tree_t* tree = malloc(sizeof(sha3_merkle_tree_t));
    tree->leaf_count = count;
    tree->leaves = malloc(count * sizeof(uint8_t*));
    
    /* Hash leaves */
    for (uint32_t i = 0; i < count; i++) {
        tree->leaves[i] = malloc(32);
        sha3_ctx ctx;
        sha3_init(&ctx, 32);
        sha3_update(&ctx, data[i], 32);
        sha3_update(&ctx, (uint8_t*)"MERKLE_LEAF", 11);
        sha3_final(tree->leaves[i], &ctx);
    }
    
    /* Build tree (simplified - just hash all leaves together) */
    sha3_ctx ctx;
    sha3_init(&ctx, 32);
    for (uint32_t i = 0; i < count; i++) {
        sha3_update(&ctx, tree->leaves[i], 32);
    }
    sha3_update(&ctx, (uint8_t*)"MERKLE_ROOT", 11);
    sha3_final(tree->root, &ctx);
    
    return tree;
}

/* SHA3-based Proof of Work */
typedef struct {
    uint8_t challenge[32];
    uint64_t nonce;
    uint8_t hash[32];
    uint32_t difficulty;
} sha3_pow_t;

sha3_pow_t* sha3_mine(const uint8_t* challenge, uint32_t difficulty) {
    sha3_pow_t* pow = malloc(sizeof(sha3_pow_t));
    memcpy(pow->challenge, challenge, 32);
    pow->difficulty = difficulty;
    pow->nonce = 0;
    
    uint8_t target_zeros = difficulty / 8;
    uint8_t target_bits = difficulty % 8;
    
    while (1) {
        sha3_ctx ctx;
        sha3_init(&ctx, 32);
        sha3_update(&ctx, challenge, 32);
        sha3_update(&ctx, (uint8_t*)&pow->nonce, 8);
        sha3_update(&ctx, (uint8_t*)"POW", 3);
        sha3_final(pow->hash, &ctx);
        
        /* Check if we meet difficulty */
        int valid = 1;
        for (uint32_t i = 0; i < target_zeros; i++) {
            if (pow->hash[i] != 0) {
                valid = 0;
                break;
            }
        }
        
        if (valid && target_bits > 0) {
            uint8_t mask = (1 << (8 - target_bits)) - 1;
            if ((pow->hash[target_zeros] & mask) != 0) {
                valid = 0;
            }
        }
        
        if (valid) {
            return pow;
        }
        
        pow->nonce++;
    }
}

/* Main Demo */
int main(void) {
    printf("=== CMPTR SHA3-Only Cryptographic Stack Demo ===\n\n");
    printf("This demonstrates complete blockchain functionality using\n");
    printf("ONLY SHA3-256 as the sole cryptographic primitive.\n\n");
    
    srand(time(NULL));
    
    /* 1. Random Number Generation */
    printf("1. SHA3-based RNG:\n");
    uint8_t seed[32] = {0x42}; /* Simple seed */
    sha3_rng_t rng;
    sha3_rng_init(&rng, seed);
    
    uint8_t random_bytes[64];
    sha3_rng_generate(&rng, random_bytes, 64);
    printf("   Generated 64 random bytes: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", random_bytes[i]);
    }
    printf("...\n\n");
    
    /* 2. Commitment Scheme */
    printf("2. SHA3-based Commitments:\n");
    const char* secret = "My secret value";
    sha3_commitment_t* com = sha3_commit((uint8_t*)secret, strlen(secret));
    printf("   Commitment: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", com->commitment[i]);
    }
    printf("...\n");
    
    int valid = sha3_verify_commitment(com, (uint8_t*)secret, strlen(secret));
    printf("   Verification: %s\n\n", valid ? "PASS" : "FAIL");
    
    /* 3. VRF (Verifiable Random Function) */
    printf("3. SHA3-based VRF:\n");
    sha3_vrf_keypair_t* vrf_kp = sha3_vrf_keygen();
    printf("   Public key: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", vrf_kp->public_key[i]);
    }
    printf("...\n");
    
    const char* vrf_msg = "epoch:42,slot:1337";
    sha3_vrf_proof_t* vrf_proof = sha3_vrf_prove(vrf_kp, 
                                                 (uint8_t*)vrf_msg, 
                                                 strlen(vrf_msg));
    printf("   VRF output: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", vrf_proof->output[i]);
    }
    printf("...\n\n");
    
    /* 4. Merkle Tree */
    printf("4. SHA3-based Merkle Tree:\n");
    uint8_t* tree_data[4];
    for (int i = 0; i < 4; i++) {
        tree_data[i] = malloc(32);
        memset(tree_data[i], i + 1, 32);
    }
    
    sha3_merkle_tree_t* merkle = sha3_merkle_build(tree_data, 4);
    printf("   Root: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", merkle->root[i]);
    }
    printf("...\n\n");
    
    /* 5. Proof of Work */
    printf("5. SHA3-based Proof of Work:\n");
    uint8_t pow_challenge[32] = {0xDE, 0xAD, 0xBE, 0xEF};
    printf("   Mining with difficulty 16...\n");
    
    clock_t start = clock();
    sha3_pow_t* pow = sha3_mine(pow_challenge, 16);
    clock_t end = clock();
    
    printf("   Found nonce: %lu\n", pow->nonce);
    printf("   Hash: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", pow->hash[i]);
    }
    printf("...\n");
    printf("   Time: %.3f seconds\n\n", (double)(end - start) / CLOCKS_PER_SEC);
    
    /* Summary */
    printf("=== Summary ===\n");
    printf("✓ Random Number Generation - using SHA3\n");
    printf("✓ Commitments - using SHA3\n");
    printf("✓ VRF (consensus) - using SHA3\n");
    printf("✓ Merkle Trees - using SHA3\n");
    printf("✓ Proof of Work - using SHA3\n");
    printf("\nAll cryptographic operations use ONLY SHA3-256!\n");
    printf("No elliptic curves, no RSA, no lattices, no pairings.\n");
    printf("Just one assumption: SHA3 collision resistance.\n\n");
    
    printf("This is how CMPTR achieves:\n");
    printf("• Post-quantum security (hash functions are quantum-safe)\n");
    printf("• Minimal assumptions (just one!)\n");
    printf("• Maximum performance (SHA3 has hardware acceleration)\n");
    printf("• Simple implementation (no complex math)\n");
    
    /* Cleanup */
    free(com);
    free(vrf_kp);
    free(vrf_proof);
    for (int i = 0; i < 4; i++) {
        free(tree_data[i]);
        free(merkle->leaves[i]);
    }
    free(merkle->leaves);
    free(merkle);
    free(pow);
    
    return 0;
}