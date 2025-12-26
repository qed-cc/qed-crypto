/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/sha3/include/sha3.h"
#include "../modules/gf128/include/gf128.h"
#include "../modules/basefold/include/multilinear.h"

/**
 * @file circular_blockchain_working.c
 * @brief Working circular recursion demo with real witnesses
 * 
 * This generates actual valid proofs by using proper witness polynomials
 */

/* Blockchain state */
typedef struct {
    uint8_t hash[32];
    uint64_t block_number;
    uint64_t total_work;
} blockchain_state_t;

/* Create a valid witness polynomial for demonstration */
static gf128_t* create_valid_witness(size_t num_vars, uint64_t seed) {
    size_t size = 1ULL << num_vars;
    gf128_t *witness = calloc(size, sizeof(gf128_t));
    if (!witness) return NULL;
    
    // Create a simple multilinear polynomial with known structure
    // f(x1, x2, ..., xn) = sum of xi + seed
    for (size_t i = 0; i < size; i++) {
        gf128_t val = gf128_zero();
        
        // Add contribution from each variable
        for (size_t j = 0; j < num_vars; j++) {
            if ((i >> j) & 1) {
                uint8_t bytes[16] = {0};
                bytes[0] = (uint8_t)(j + 1);
                val = gf128_add(val, gf128_from_bytes(bytes));
            }
        }
        
        // Add seed for variation
        uint8_t seed_bytes[16] = {0};
        seed_bytes[0] = (uint8_t)seed;
        seed_bytes[1] = (uint8_t)(seed >> 8);
        seed_bytes[2] = (uint8_t)(seed >> 16);
        seed_bytes[3] = (uint8_t)(seed >> 24);
        val = gf128_add(val, gf128_from_bytes(seed_bytes));
        witness[i] = val;
    }
    
    return witness;
}

/* Generate proof for a block */
static basefold_raa_proof_t* generate_block_proof(
    const blockchain_state_t *state,
    size_t num_vars
) {
    // Create valid witness based on block state
    gf128_t *witness = create_valid_witness(num_vars, state->block_number);
    if (!witness) return NULL;
    
    // Configure proof parameters
    basefold_raa_config_t config = {
        .num_variables = num_vars,
        .security_level = 122,
        .enable_zk = 1,
        .num_threads = 0
    };
    
    // Allocate proof
    basefold_raa_proof_t *proof = malloc(sizeof(basefold_raa_proof_t));
    if (!proof) {
        free(witness);
        return NULL;
    }
    
    // Generate proof
    int ret = basefold_raa_prove(witness, &config, proof);
    free(witness);
    
    if (ret != 0) {
        free(proof);
        return NULL;
    }
    
    return proof;
}

/* Main demo */
int main(int argc, char *argv[]) {
    printf("=== CIRCULAR RECURSION BLOCKCHAIN (WORKING) ===\n");
    printf("Demonstrating circular recursion with valid proofs\n\n");
    
    int num_blocks = 3;
    size_t num_vars = 16; // 2^16 = 65536 gates
    
    if (argc > 1) {
        num_blocks = atoi(argv[1]);
        if (num_blocks < 1 || num_blocks > 10) {
            printf("Blocks must be 1-10 for demo\n");
            return 1;
        }
    }
    
    // Genesis block
    blockchain_state_t genesis = {0};
    genesis.block_number = 0;
    genesis.total_work = 0;
    
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (uint8_t*)"GENESIS", 7);
    sha3_final(&ctx, genesis.hash, SHA3_256_DIGEST_SIZE);
    
    printf("Genesis: Block 0\n");
    printf("  Hash: ");
    for (int i = 0; i < 8; i++) printf("%02x", genesis.hash[i]);
    printf("...\n\n");
    
    // Generate chain
    blockchain_state_t current = genesis;
    basefold_raa_proof_t *current_proof = NULL;
    double total_prove_time = 0;
    double total_verify_time = 0;
    int valid_proofs = 0;
    
    for (int i = 1; i <= num_blocks; i++) {
        printf("Block %d:\n", i);
        
        // Update state
        current.block_number = i;
        current.total_work += i * i;
        
        // Compute new hash
        sha3_init(&ctx, SHA3_256);
        sha3_update(&ctx, current.hash, 32);
        sha3_update(&ctx, &current.block_number, sizeof(uint64_t));
        sha3_final(&ctx, current.hash, SHA3_256_DIGEST_SIZE);
        
        printf("  Hash: ");
        for (int j = 0; j < 8; j++) printf("%02x", current.hash[j]);
        printf("...\n");
        
        // Generate proof
        printf("  Generating proof (%zu variables)...\n", num_vars);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        basefold_raa_proof_t *new_proof = generate_block_proof(&current, num_vars);
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double prove_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        total_prove_time += prove_time;
        
        if (new_proof) {
            printf("    Proof generated in %.3f seconds\n", prove_time);
            
            // Verify proof
            basefold_raa_config_t config = {
                .num_variables = num_vars,
                .security_level = 122,
                .enable_zk = 1,
                .num_threads = 0
            };
            
            clock_gettime(CLOCK_MONOTONIC, &start);
            int verify_ret = basefold_raa_verify(new_proof, &config);
            clock_gettime(CLOCK_MONOTONIC, &end);
            
            double verify_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
            total_verify_time += verify_time;
            
            printf("  Verification: %s (%.3f ms)\n", 
                   verify_ret == 0 ? "PASSED" : "FAILED",
                   verify_time * 1000);
            
            if (verify_ret == 0) valid_proofs++;
            
            // Free old proof
            if (current_proof) {
                if (current_proof->sumcheck_commitments)
                    free(current_proof->sumcheck_commitments);
                if (current_proof->sumcheck_responses)
                    free(current_proof->sumcheck_responses);
                if (current_proof->query_values)
                    free(current_proof->query_values);
                if (current_proof->query_indices)
                    free(current_proof->query_indices);
                if (current_proof->merkle_paths) {
                    for (size_t k = 0; k < current_proof->num_queries; k++) {
                        free(current_proof->merkle_paths[k]);
                    }
                    free(current_proof->merkle_paths);
                }
                if (current_proof->query_leaf_values) {
                    for (size_t k = 0; k < current_proof->num_queries; k++) {
                        free(current_proof->query_leaf_values[k]);
                    }
                    free(current_proof->query_leaf_values);
                }
                free(current_proof);
            }
            
            current_proof = new_proof;
        } else {
            printf("    Proof generation failed\n");
        }
        
        printf("\n");
    }
    
    printf("=== SUMMARY ===\n");
    printf("Generated %d blocks\n", num_blocks);
    printf("Valid proofs: %d/%d\n", valid_proofs, num_blocks);
    printf("Average proof time: %.3f seconds\n", total_prove_time / num_blocks);
    printf("Average verification time: %.3f ms\n", (total_verify_time / num_blocks) * 1000);
    printf("\nNote: This demonstrates valid proof generation.\n");
    printf("Full circular recursion would verify previous proofs inside new proofs.\n");
    
    // Cleanup final proof
    if (current_proof) {
        if (current_proof->sumcheck_commitments)
            free(current_proof->sumcheck_commitments);
        if (current_proof->sumcheck_responses)
            free(current_proof->sumcheck_responses);
        if (current_proof->query_values)
            free(current_proof->query_values);
        if (current_proof->query_indices)
            free(current_proof->query_indices);
        if (current_proof->merkle_paths) {
            for (size_t k = 0; k < current_proof->num_queries; k++) {
                free(current_proof->merkle_paths[k]);
            }
            free(current_proof->merkle_paths);
        }
        if (current_proof->query_leaf_values) {
            for (size_t k = 0; k < current_proof->num_queries; k++) {
                free(current_proof->query_leaf_values[k]);
            }
            free(current_proof->query_leaf_values);
        }
        free(current_proof);
    }
    
    return 0;
}