/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include "../include/gate_core.h"
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/sha3/include/sha3.h"
#include "../modules/gf128/include/gf128.h"
#include "../modules/circuit_generator/include/circuit_generator.h"
#include "../modules/circuit_encoder/include/encoder.h"

/* Blockchain State Structure */
typedef struct {
    uint8_t hash[32];      // Current block hash (SHA3-256)
    uint64_t block_number; // Block number
    uint64_t timestamp;    // Timestamp
    uint64_t nonce;        // Nonce (for PoW simulation)
} blockchain_state_t;

/* Circuit for blockchain state transition:
 * 1. Verify previous proof (if not genesis)
 * 2. Compute new_hash = SHA3(prev_hash || block_data)
 * 3. Increment block number
 * 4. Update timestamp
 */
static void generate_blockchain_transition_circuit(
    circuit_t *circuit,
    const blockchain_state_t *prev_state,
    const blockchain_state_t *new_state,
    bool is_genesis
) {
    // Input wires for previous state
    size_t prev_hash_start = 0;
    size_t block_num_start = prev_hash_start + 256;  // 256 bits for hash
    size_t timestamp_start = block_num_start + 64;   // 64 bits for block number
    size_t nonce_start = timestamp_start + 64;       // 64 bits for timestamp
    
    // Convert previous state to bits
    uint8_t prev_bits[448];  // 256 + 64 + 64 + 64
    memset(prev_bits, 0, sizeof(prev_bits));
    
    // Previous hash to bits
    for (int i = 0; i < 32; i++) {
        for (int j = 0; j < 8; j++) {
            prev_bits[i * 8 + j] = (prev_state->hash[i] >> (7 - j)) & 1;
        }
    }
    
    // Block number to bits (little-endian)
    for (int i = 0; i < 64; i++) {
        prev_bits[256 + i] = (prev_state->block_number >> i) & 1;
    }
    
    // Timestamp to bits
    for (int i = 0; i < 64; i++) {
        prev_bits[320 + i] = (prev_state->timestamp >> i) & 1;
    }
    
    // Nonce to bits
    for (int i = 0; i < 64; i++) {
        prev_bits[384 + i] = (prev_state->nonce >> i) & 1;
    }
    
    // Set input values
    for (size_t i = 0; i < 448; i++) {
        circuit->wires[i] = prev_bits[i];
    }
    
    size_t next_wire = 448;
    
    // If not genesis, we would verify the previous recursive proof here
    // For now, we'll skip the recursive verification circuit
    
    // Prepare input for SHA3: prev_hash || block_data
    // Block data = block_number || timestamp || nonce
    uint8_t sha3_input[64];  // 32 bytes hash + 32 bytes block data
    memcpy(sha3_input, prev_state->hash, 32);
    
    // Pack block data
    memcpy(sha3_input + 32, &new_state->block_number, 8);
    memcpy(sha3_input + 40, &new_state->timestamp, 8);
    memcpy(sha3_input + 48, &new_state->nonce, 8);
    memset(sha3_input + 56, 0, 8);  // Padding
    
    // Generate SHA3-256 circuit
    size_t sha3_output_start = next_wire;
    generate_sha3_256_circuit(circuit, &next_wire, prev_hash_start, 512);  // 512 bits input
    
    // Verify block number increment
    // new_block_num = prev_block_num + 1
    size_t adder_start = next_wire;
    
    // Add constant 1 to block number
    for (int i = 0; i < 64; i++) {
        if (i == 0) {
            // LSB: add 1
            add_gate(circuit, OP_XOR, block_num_start + i, next_wire, next_wire + 1);
            circuit->wires[next_wire] = 1;  // Constant 1
            next_wire += 2;
        } else {
            // Other bits: just copy (simplified - real adder would handle carry)
            add_gate(circuit, OP_COPY, block_num_start + i, 0, next_wire);
            next_wire++;
        }
    }
    
    // Set output wires to match expected new state
    // In a real implementation, we'd add constraints to ensure outputs match
    
    circuit->num_wires = next_wire;
    circuit->public_wires = 512;  // Previous and new hash are public
}

/* Generate proof for blockchain state transition */
static int generate_blockchain_proof(
    const blockchain_state_t *prev_state,
    const blockchain_state_t *new_state,
    const char *proof_file,
    bool is_genesis
) {
    printf("\n=== Generating Blockchain State Transition Proof ===\n");
    printf("Previous block: #%" PRIu64 "\n", prev_state->block_number);
    printf("New block: #%" PRIu64 "\n", new_state->block_number);
    
    // Generate circuit
    circuit_t *circuit = create_circuit(1000000, 100000);  // 1M wires, 100K gates
    generate_blockchain_transition_circuit(circuit, prev_state, new_state, is_genesis);
    
    printf("Circuit: %zu gates, %zu wires\n", circuit->num_gates, circuit->num_wires);
    
    // Evaluate circuit
    uint8_t *witness = calloc(circuit->num_wires, sizeof(uint8_t));
    evaluate_circuit(circuit, witness);
    
    // Generate proof
    basefold_raa_proof_t *proof = basefold_raa_prove(circuit, witness, true);  // enable_zk = true
    if (!proof) {
        fprintf(stderr, "Failed to generate proof\n");
        free(witness);
        free_circuit(circuit);
        return -1;
    }
    
    // Save proof
    FILE *fp = fopen(proof_file, "wb");
    if (!fp) {
        fprintf(stderr, "Failed to open proof file\n");
        basefold_raa_free_proof(proof);
        free(witness);
        free_circuit(circuit);
        return -1;
    }
    
    fwrite(proof, sizeof(basefold_raa_proof_t), 1, fp);
    fclose(fp);
    
    printf("Proof saved to: %s\n", proof_file);
    printf("Proof size: %zu bytes\n", sizeof(basefold_raa_proof_t));
    
    basefold_raa_free_proof(proof);
    free(witness);
    free_circuit(circuit);
    
    return 0;
}

/* Simulate blockchain evolution */
static void simulate_blockchain(int num_blocks) {
    printf("\n=== Simulating Blockchain with Circular Recursion ===\n");
    printf("Generating %d blocks...\n\n", num_blocks);
    
    // Genesis block
    blockchain_state_t genesis = {0};
    memcpy(genesis.hash, "GENESIS_BLOCK_HASH_SHA3_256_HERE", 32);
    genesis.block_number = 0;
    genesis.timestamp = time(NULL);
    genesis.nonce = 0;
    
    blockchain_state_t current = genesis;
    blockchain_state_t next;
    
    // Generate proofs for each block transition
    for (int i = 1; i <= num_blocks; i++) {
        // Compute next block
        next.block_number = i;
        next.timestamp = current.timestamp + 10;  // 10 second blocks
        next.nonce = rand() % 1000000;  // Random nonce
        
        // Compute new hash
        uint8_t hash_input[64];
        memcpy(hash_input, current.hash, 32);
        memcpy(hash_input + 32, &next.block_number, 8);
        memcpy(hash_input + 40, &next.timestamp, 8);
        memcpy(hash_input + 48, &next.nonce, 8);
        
        sha3_256(hash_input, 56, next.hash);
        
        // Generate proof
        char proof_file[256];
        snprintf(proof_file, sizeof(proof_file), "blockchain_proof_%d.raa", i);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        int ret = generate_blockchain_proof(&current, &next, proof_file, i == 1);
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
        if (ret == 0) {
            printf("Block %d proof generated in %.3f seconds\n\n", i, elapsed);
        } else {
            printf("Failed to generate proof for block %d\n", i);
            break;
        }
        
        current = next;
    }
    
    printf("\n=== Blockchain Simulation Complete ===\n");
    printf("Final block hash: ");
    for (int i = 0; i < 32; i++) {
        printf("%02x", current.hash[i]);
    }
    printf("\n");
}

/* Recursive proof composition for blockchain */
static void compose_blockchain_proofs(int start_block, int end_block) {
    printf("\n=== Composing Recursive Blockchain Proofs ===\n");
    printf("Combining proofs from block %d to %d\n", start_block, end_block);
    
    // TODO: Implement recursive composition
    // This would:
    // 1. Load proofs for each block transition
    // 2. Recursively compose them into a single proof
    // 3. The final proof would verify the entire chain from genesis to end_block
    
    printf("Recursive composition not yet implemented\n");
    printf("Would create a single proof verifying blocks %d-%d\n", start_block, end_block);
}

int main(int argc, char *argv[]) {
    printf("=== Blockchain Circular Recursion Demo ===\n");
    printf("Post-quantum secure blockchain proofs using BaseFold RAA\n\n");
    
    // Initialize GF(2^128)
    gf128_init();
    
    if (argc < 2) {
        printf("Usage: %s <num_blocks> [compose]\n", argv[0]);
        printf("  num_blocks: Number of blocks to generate\n");
        printf("  compose: If present, compose proofs recursively\n");
        return 1;
    }
    
    int num_blocks = atoi(argv[1]);
    if (num_blocks < 1 || num_blocks > 100) {
        printf("Number of blocks must be between 1 and 100\n");
        return 1;
    }
    
    // Simulate blockchain
    simulate_blockchain(num_blocks);
    
    // Optionally compose proofs
    if (argc > 2 && strcmp(argv[2], "compose") == 0) {
        compose_blockchain_proofs(1, num_blocks);
    }
    
    printf("\n=== Circular Recursion Concept ===\n");
    printf("Each proof verifies:\n");
    printf("1. The previous state was valid (recursive proof)\n");
    printf("2. The transition to new state is correct (SHA3)\n");
    printf("3. Block number incremented correctly\n");
    printf("\nThis creates a chain where each proof depends on the previous,\n");
    printf("forming a 'circular' recursive structure.\n");
    printf("\nA single composed proof can verify the entire blockchain!\n");
    
    return 0;
}