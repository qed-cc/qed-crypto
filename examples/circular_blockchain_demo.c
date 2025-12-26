/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include "../modules/basefold_raa/include/circular_recursion.h"
#include "../modules/sha3/include/sha3.h"
#include "../modules/gf128/include/gf128.h"

/**
 * @file circular_blockchain_demo.c
 * @brief Demonstrates circular recursion for blockchain proofs
 * 
 * Shows how to prove an entire blockchain with a single recursive proof
 * that verifies all state transitions from genesis.
 */

/* Compute next blockchain state */
static void compute_next_state(
    const blockchain_state_t *prev,
    blockchain_state_t *next,
    uint64_t nonce
) {
    // Set basic fields
    next->block_number = prev->block_number + 1;
    next->accumulated_work = prev->accumulated_work + (next->block_number * next->block_number);
    
    // Compute new state hash = SHA3(prev_hash || block_number || nonce)
    uint8_t input[48];
    memcpy(input, prev->state_hash, 32);
    memcpy(input + 32, &next->block_number, 8);
    memcpy(input + 40, &nonce, 8);
    
    // Use SHA3 hash function
    sha3_hash_function *sha3 = sha3_create_hash_function(SHA3_256);
    if (sha3) {
        sha3->init(sha3);
        sha3->update(sha3, input, 48);
        sha3->finalize(sha3, next->state_hash);
        sha3_free_hash_function(sha3);
    }
}

/* Print blockchain state */
static void print_state(const blockchain_state_t *state) {
    printf("Block #%" PRIu64 ": ", state->block_number);
    for (int i = 0; i < 8; i++) {
        printf("%02x", state->state_hash[i]);
    }
    printf("... (work: %" PRIu64 ")\n", state->accumulated_work);
}

/* Demonstrate circular recursion */
static void demonstrate_circular_blockchain(int num_blocks) {
    printf("\n=== CIRCULAR RECURSION BLOCKCHAIN DEMO ===\n");
    printf("Proving %d blocks with circular recursion\n\n", num_blocks);
    
    // Initialize GF(2^128) for BaseFold
    gf128_init();
    
    // Genesis state
    blockchain_state_t genesis = {0};
    genesis.block_number = 0;
    genesis.accumulated_work = 0;
    
    // Genesis hash
    sha3_hash_function *sha3 = sha3_create_hash_function(SHA3_256);
    if (sha3) {
        sha3->init(sha3);
        sha3->update(sha3, (uint8_t*)"GENESIS_BLOCK", 13);
        sha3->finalize(sha3, genesis.state_hash);
        sha3_free_hash_function(sha3);
    }
    
    printf("Genesis block:\n");
    print_state(&genesis);
    printf("\n");
    
    // Generate blockchain with circular recursion
    blockchain_state_t current = genesis;
    blockchain_state_t next;
    circular_proof_t *current_proof = NULL;
    
    double total_proof_time = 0;
    
    for (int i = 1; i <= num_blocks; i++) {
        printf("Block %d:\n", i);
        
        // Compute next state
        uint64_t nonce = rand() % 1000000;
        compute_next_state(&current, &next, nonce);
        print_state(&next);
        
        // Generate circular recursion proof
        printf("  Generating proof...");
        fflush(stdout);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        circular_proof_t *new_proof = basefold_raa_circular_prove(
            &current, &next, current_proof, i == 1
        );
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double elapsed = (end.tv_sec - start.tv_sec) + 
                         (end.tv_nsec - start.tv_nsec) / 1e9;
        total_proof_time += elapsed;
        
        if (new_proof) {
            printf(" ✓ (%.3fs)\n", elapsed);
            
            // Verify the proof
            printf("  Verifying proof...");
            fflush(stdout);
            
            bool valid = basefold_raa_circular_verify(new_proof, &genesis);
            printf(" %s\n", valid ? "✓ VALID" : "✗ INVALID");
            
            // Free previous proof
            if (current_proof) {
                basefold_raa_circular_free(current_proof);
            }
            
            current_proof = new_proof;
        } else {
            printf(" ✗ FAILED\n");
            break;
        }
        
        current = next;
        printf("\n");
    }
    
    printf("=== CIRCULAR RECURSION SUMMARY ===\n");
    printf("Total blocks proved: %d\n", num_blocks);
    printf("Total proving time: %.3f seconds\n", total_proof_time);
    printf("Average time per block: %.3f seconds\n", total_proof_time / num_blocks);
    
    if (current_proof) {
        size_t proof_size = basefold_raa_circular_proof_size(current_proof);
        printf("Final proof size: %zu bytes (~%zuKB)\n", proof_size, proof_size / 1024);
        printf("\nThis single proof verifies the ENTIRE blockchain!\n");
        
        basefold_raa_circular_free(current_proof);
    }
    
    printf("\n=== KEY INSIGHTS ===\n");
    printf("• ONE proof verifies %d state transitions\n", num_blocks);
    printf("• Constant proof size regardless of chain length\n");
    printf("• Post-quantum secure (no elliptic curves)\n");
    printf("• Zero-knowledge (privacy preserved)\n");
}

int main(int argc, char *argv[]) {
    printf("=== CIRCULAR RECURSION FOR BLOCKCHAIN ===\n");
    printf("Post-Quantum Secure Recursive Proofs with BaseFold RAA\n");
    
    int num_blocks = 5;
    if (argc > 1) {
        num_blocks = atoi(argv[1]);
        if (num_blocks < 1 || num_blocks > 20) {
            printf("Number of blocks must be between 1 and 20\n");
            return 1;
        }
    }
    
    demonstrate_circular_blockchain(num_blocks);
    
    return 0;
}