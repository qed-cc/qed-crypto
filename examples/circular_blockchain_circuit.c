/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/basefold_raa/include/circuit_witness_generator.h"
#include "../modules/basefold_raa/include/state_transition.h"
#include "../modules/sha3/include/sha3.h"
#include "../modules/gf128/include/gf128.h"
#include "../modules/circuit_evaluator/include/evaluator.h"

/**
 * @file circular_blockchain_circuit.c
 * @brief Circular recursion using actual circuit witnesses
 * 
 * This version generates witnesses from actual circuit evaluations,
 * which should satisfy the sumcheck protocol.
 */

/* Blockchain state */
typedef struct {
    uint8_t hash[32];
    uint64_t block_number;
    uint64_t total_work;
} blockchain_state_t;

/* Generate proof using circuit witness */
static basefold_raa_proof_t* generate_circuit_proof(
    circuit_t *circuit,
    size_t num_vars
) {
    printf("  Generating circuit witness (%zu variables)...\n", num_vars);
    
    // Generate witness by evaluating circuit on all inputs
    gf128_t *witness = generate_circuit_witness(circuit, num_vars);
    if (!witness) {
        printf("    Failed to generate witness\n");
        return NULL;
    }
    
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
    printf("  Generating proof from circuit witness...\n");
    int ret = basefold_raa_prove(witness, &config, proof);
    free(witness);
    
    if (ret != 0) {
        printf("    Proof generation failed: %d\n", ret);
        free(proof);
        return NULL;
    }
    
    return proof;
}

/* Create a simple demonstration circuit */
static circuit_t* create_demo_circuit(size_t num_inputs) {
    // For demo: Create XOR of all inputs
    // This gives a simple but valid circuit
    
    size_t num_gates = num_inputs - 1;
    circuit_t *circuit = evaluator_init_circuit(num_inputs, num_gates, 1);
    if (!circuit) return NULL;
    
    // Wire IDs: 0=const0, 1=const1, 2...(num_inputs+1)=inputs
    uint32_t current_wire = 2; // First input
    uint32_t next_wire = 2 + num_inputs; // First gate output
    
    // XOR all inputs together
    for (size_t i = 0; i < num_gates; i++) {
        circuit->gates[i].type = GATE_XOR;
        if (i == 0) {
            // First gate: XOR first two inputs
            circuit->gates[i].input1 = 2;
            circuit->gates[i].input2 = 3;
        } else {
            // Subsequent gates: XOR previous result with next input
            circuit->gates[i].input1 = next_wire - 1;
            circuit->gates[i].input2 = 2 + i + 1;
        }
        circuit->gates[i].output = next_wire++;
    }
    
    // Set output to last gate's output
    circuit->output_wires[0] = next_wire - 1;
    circuit->num_outputs = 1;
    
    return circuit;
}

/* Main demo */
int main(int argc, char *argv[]) {
    printf("=== CIRCULAR RECURSION WITH CIRCUIT WITNESSES ===\n");
    printf("Using actual circuit evaluations for valid proofs\n\n");
    
    int num_blocks = 3;
    size_t circuit_inputs = 16; // Circuit has 16 inputs
    size_t num_vars = 16; // 2^16 = 65536 witness size
    
    if (argc > 1) {
        num_blocks = atoi(argv[1]);
        if (num_blocks < 1 || num_blocks > 10) {
            printf("Blocks must be 1-10 for demo\n");
            return 1;
        }
    }
    
    // Test with simple circuit first
    printf("Step 1: Testing with simple XOR circuit\n");
    printf("----------------------------------------\n");
    
    circuit_t *test_circuit = create_simple_test_circuit();
    if (!test_circuit) {
        printf("Failed to create test circuit\n");
        return 1;
    }
    
    // Generate and verify a test proof
    basefold_raa_proof_t *test_proof = generate_circuit_proof(test_circuit, 10); // 2^10 = 1024
    if (test_proof) {
        printf("  Test proof generated successfully\n");
        
        basefold_raa_config_t config = {
            .num_variables = 10,
            .security_level = 122,
            .enable_zk = 1,
            .num_threads = 0
        };
        
        int verify_ret = basefold_raa_verify(test_proof, &config);
        printf("  Verification: %s\n\n", verify_ret == 0 ? "PASSED ✓" : "FAILED ✗");
        
        // Cleanup test proof
        if (test_proof->sumcheck_commitments) free(test_proof->sumcheck_commitments);
        if (test_proof->sumcheck_responses) free(test_proof->sumcheck_responses);
        if (test_proof->query_values) free(test_proof->query_values);
        if (test_proof->query_indices) free(test_proof->query_indices);
        if (test_proof->merkle_paths) {
            for (size_t i = 0; i < test_proof->num_queries; i++) {
                free(test_proof->merkle_paths[i]);
            }
            free(test_proof->merkle_paths);
        }
        if (test_proof->query_leaf_values) {
            for (size_t i = 0; i < test_proof->num_queries; i++) {
                free(test_proof->query_leaf_values[i]);
            }
            free(test_proof->query_leaf_values);
        }
        free(test_proof);
    }
    evaluator_free_circuit(test_circuit);
    
    // Now do blockchain demo
    printf("Step 2: Blockchain with circuit-based proofs\n");
    printf("-------------------------------------------\n");
    
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
        
        // Create circuit for this block
        circuit_t *block_circuit = create_demo_circuit(circuit_inputs);
        if (!block_circuit) {
            printf("  Failed to create circuit\n");
            continue;
        }
        
        // Generate proof
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        basefold_raa_proof_t *new_proof = generate_circuit_proof(block_circuit, num_vars);
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double prove_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
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
            
            printf("  Verification: %s (%.3f ms)\n", 
                   verify_ret == 0 ? "PASSED ✓" : "FAILED ✗",
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
        
        evaluator_free_circuit(block_circuit);
        printf("\n");
    }
    
    printf("=== SUMMARY ===\n");
    printf("Generated %d blocks\n", num_blocks);
    printf("Valid proofs: %d/%d\n", valid_proofs, num_blocks);
    
    if (valid_proofs > 0) {
        printf("\n✓ SUCCESS: Generated valid proofs using circuit witnesses!\n");
        printf("Next step: Integrate recursive verifier circuit for true circular recursion.\n");
    }
    
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