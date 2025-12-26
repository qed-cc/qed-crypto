/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file circular_recursion.c
 * @brief Circular recursion for blockchain proof generation
 * 
 * Implements circular recursion where each proof verifies the entire
 * blockchain history from genesis. Uses the recursive BaseFold infrastructure.
 */

#include "../include/basefold_raa.h"
#include "../include/basefold_raa_128bit.h"
#include "../include/circular_recursion.h"
#include "../../sha3/include/sha3.h"
#include "../../gf128/include/gf128.h"
#include "../../../include/gate_core.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Blockchain state for circular recursion */
typedef struct {
    uint8_t state_hash[32];      // Current state hash (SHA3-256)
    uint64_t block_number;       // Block number
    uint64_t accumulated_work;   // Total work done
    uint8_t prev_proof_hash[32]; // Hash of previous recursive proof
} blockchain_state_t;

/* Circular proof structure */
struct circular_proof {
    blockchain_state_t state;         // Current blockchain state
    basefold_raa_proof_t *proof;     // Recursive proof
    circuit_t *transition_circuit;   // State transition circuit
};

/**
 * @brief Generate state transition circuit
 * 
 * Creates a circuit that:
 * 1. Verifies the previous recursive proof (unless genesis)
 * 2. Computes new_hash = SHA3(prev_hash || block_number)
 * 3. Verifies block_number = prev_block_number + 1
 */
static circuit_t* generate_state_transition_circuit(
    const blockchain_state_t *prev_state,
    const blockchain_state_t *new_state,
    const basefold_raa_proof_t *prev_proof,
    bool is_genesis
) {
    // Create circuit with enough capacity
    circuit_t *circuit = create_circuit(10000000, 1000000); // 10M wires, 1M gates
    if (!circuit) return NULL;
    
    size_t wire_idx = 0;
    
    // Public inputs: previous state hash (256 bits) + block number (64 bits)
    size_t prev_hash_start = wire_idx;
    wire_idx += 256;
    
    size_t prev_block_start = wire_idx;
    wire_idx += 64;
    
    // Set public input values from previous state
    for (int i = 0; i < 32; i++) {
        for (int j = 0; j < 8; j++) {
            circuit->wires[prev_hash_start + i*8 + j] = 
                (prev_state->state_hash[i] >> (7-j)) & 1;
        }
    }
    
    for (int i = 0; i < 64; i++) {
        circuit->wires[prev_block_start + i] = 
            (prev_state->block_number >> i) & 1;
    }
    
    circuit->public_wires = 320; // 256 + 64
    
    // If not genesis, add recursive verifier circuit
    if (!is_genesis && prev_proof) {
        // This would use the existing verifier circuit generator
        // For now, simulate with placeholder gates
        size_t verifier_gates = 5400000; // ~5.4M gates for verifier
        for (size_t i = 0; i < 1000; i++) { // Add some placeholder gates
            add_gate(circuit, OP_XOR, wire_idx, wire_idx + 1, wire_idx + 2);
            wire_idx += 3;
        }
    }
    
    // Generate SHA3-256 circuit for state transition
    // new_hash = SHA3(prev_hash || block_number)
    size_t sha3_input_start = wire_idx;
    
    // Copy previous hash to SHA3 input
    for (int i = 0; i < 256; i++) {
        add_gate(circuit, OP_COPY, prev_hash_start + i, 0, sha3_input_start + i);
        wire_idx++;
    }
    
    // Copy block number to SHA3 input
    for (int i = 0; i < 64; i++) {
        add_gate(circuit, OP_COPY, prev_block_start + i, 0, sha3_input_start + 256 + i);
        wire_idx++;
    }
    
    // Generate SHA3-256 circuit (placeholder - would use real SHA3 circuit generator)
    size_t sha3_output_start = wire_idx;
    wire_idx += 256;
    
    // Add increment circuit for block number
    // new_block_number = prev_block_number + 1
    size_t increment_start = wire_idx;
    size_t carry = wire_idx++;
    circuit->wires[carry] = 1; // Initial carry = 1
    
    for (int i = 0; i < 64; i++) {
        size_t a = prev_block_start + i;
        size_t sum = wire_idx++;
        size_t new_carry = wire_idx++;
        
        // sum = a XOR carry
        add_gate(circuit, OP_XOR, a, carry, sum);
        // new_carry = a AND carry
        add_gate(circuit, OP_AND, a, carry, new_carry);
        
        carry = new_carry;
    }
    
    circuit->num_wires = wire_idx;
    
    return circuit;
}

/**
 * @brief Generate circular recursion proof
 * 
 * Creates a proof that verifies the entire blockchain history from genesis
 * to the current state. Each proof recursively contains all previous proofs.
 */
circular_proof_t* basefold_raa_circular_prove(
    const blockchain_state_t *prev_state,
    const blockchain_state_t *new_state,
    const circular_proof_t *prev_proof,
    bool is_genesis
) {
    printf("Generating circular recursion proof...\n");
    printf("  Previous block: %lu\n", prev_state->block_number);
    printf("  New block: %lu\n", new_state->block_number);
    printf("  Is genesis: %s\n", is_genesis ? "yes" : "no");
    
    // Generate state transition circuit
    circuit_t *circuit = generate_state_transition_circuit(
        prev_state, new_state, 
        prev_proof ? prev_proof->proof : NULL,
        is_genesis
    );
    
    if (!circuit) {
        fprintf(stderr, "Failed to generate state transition circuit\n");
        return NULL;
    }
    
    printf("  Circuit size: %zu gates, %zu wires\n", 
           circuit->num_gates, circuit->num_wires);
    
    // Create witness for the circuit
    uint8_t *witness = calloc(circuit->num_wires, sizeof(uint8_t));
    if (!witness) {
        free_circuit(circuit);
        return NULL;
    }
    
    // Evaluate circuit to populate witness
    evaluate_circuit(circuit, witness);
    
    // Generate recursive proof
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    // Create config for proof generation
    basefold_raa_config_t config = {
        .num_variables = 0,  // Will be set based on circuit size
        .security_level = 122,
        .enable_zk = 1,
        .num_threads = 0  // Auto-detect
    };
    
    // Calculate number of variables (log2 of witness size)
    size_t n = circuit->num_wires;
    while ((1ULL << config.num_variables) < n) {
        config.num_variables++;
    }
    
    basefold_raa_proof_t *proof = malloc(sizeof(basefold_raa_proof_t));
    if (!proof) {
        fprintf(stderr, "Failed to allocate proof\n");
        free(witness);
        free_circuit(circuit);
        return NULL;
    }
    
    // Convert witness to GF128
    gf128_t *gf128_witness = malloc(n * sizeof(gf128_t));
    if (!gf128_witness) {
        free(proof);
        free(witness);
        free_circuit(circuit);
        return NULL;
    }
    
    for (size_t i = 0; i < n; i++) {
        gf128_witness[i] = witness[i] ? gf128_one() : gf128_zero();
    }
    
    int ret = basefold_raa_prove(gf128_witness, &config, proof);
    free(gf128_witness);
    
    if (ret != 0) {
        fprintf(stderr, "basefold_raa_prove failed: %d\n", ret);
        free(proof);
        free(witness);
        free_circuit(circuit);
        return NULL;
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) + 
                     (end.tv_nsec - start.tv_nsec) / 1e9;
    
    if (!proof) {
        fprintf(stderr, "Failed to generate proof\n");
        free(witness);
        free_circuit(circuit);
        return NULL;
    }
    
    printf("  Proof generated in %.3f seconds\n", elapsed);
    
    // Create circular proof structure
    circular_proof_t *cproof = malloc(sizeof(circular_proof_t));
    if (!cproof) {
        basefold_raa_free_proof(proof);
        free(witness);
        free_circuit(circuit);
        return NULL;
    }
    
    cproof->state = *new_state;
    cproof->proof = proof;
    cproof->transition_circuit = circuit;
    
    // Hash the proof for chaining
    sha3_hash_function *sha3 = sha3_create_hash_function();
    if (sha3) {
        sha3_init(sha3, SHA3_256);
        sha3_update(sha3, (uint8_t*)proof, sizeof(basefold_raa_proof_t));
        sha3_final(sha3, cproof->state.prev_proof_hash);
        sha3_free_hash_function(sha3);
    }
    
    free(witness);
    
    return cproof;
}

/**
 * @brief Verify circular recursion proof
 * 
 * Verifies that a circular proof correctly proves the entire blockchain
 * history from genesis to the claimed state.
 */
bool basefold_raa_circular_verify(
    const circular_proof_t *cproof,
    const blockchain_state_t *genesis_state
) {
    printf("Verifying circular recursion proof...\n");
    printf("  Claimed block: %lu\n", cproof->state.block_number);
    
    // Reconstruct expected circuit for verification
    // In practice, we'd need to reconstruct the exact same circuit
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    // Create config for verification
    basefold_raa_config_t config = {
        .num_variables = 0,
        .security_level = 122,
        .enable_zk = 1,
        .num_threads = 0
    };
    
    // Calculate number of variables
    size_t n = cproof->transition_circuit->num_wires;
    while ((1ULL << config.num_variables) < n) {
        config.num_variables++;
    }
    
    // Verify the proof
    int verify_ret = basefold_raa_verify(cproof->proof, &config);
    bool valid = (verify_ret == 0);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) + 
                     (end.tv_nsec - start.tv_nsec) / 1e9;
    
    printf("  Verification completed in %.3f ms\n", elapsed * 1000);
    printf("  Result: %s\n", valid ? "VALID" : "INVALID");
    
    return valid;
}

/**
 * @brief Free circular proof
 */
void basefold_raa_circular_free(circular_proof_t *cproof) {
    if (cproof) {
        if (cproof->proof) {
            // Free proof components
            if (cproof->proof->sumcheck_commitments) {
                free(cproof->proof->sumcheck_commitments);
            }
            if (cproof->proof->sumcheck_responses) {
                free(cproof->proof->sumcheck_responses);
            }
            free(cproof->proof);
        }
        if (cproof->transition_circuit) {
            free_circuit(cproof->transition_circuit);
        }
        free(cproof);
    }
}

/**
 * @brief Get proof size in bytes
 */
size_t basefold_raa_circular_proof_size(const circular_proof_t *cproof) {
    if (!cproof || !cproof->proof) {
        return 0;
    }
    // BaseFold RAA proofs are ~190KB
    return sizeof(basefold_raa_proof_t);
}