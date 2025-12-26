/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/basefold_raa/include/gate_witness_generator.h"
#include "../modules/sha3/include/sha3.h"
#include "../modules/gf128/include/gf128.h"

/**
 * @file circular_blockchain_gate_witness.c
 * @brief Circular recursion using proper gate constraint witnesses
 * 
 * This version uses witnesses that satisfy the gate constraint sumcheck.
 */

int main(int argc, char *argv[]) {
    printf("=== CIRCULAR BLOCKCHAIN WITH GATE WITNESSES ===\n");
    printf("Using gate constraint witnesses for valid proofs\n\n");
    
    // Step 1: Test with simple XOR witness
    printf("Step 1: Testing simple XOR gate witness\n");
    printf("---------------------------------------\n");
    
    size_t num_vars = 10; // 2^10 = 1024 witness size = 256 gates
    gf128_t *witness = generate_simple_xor_witness(num_vars);
    if (!witness) {
        printf("Failed to generate witness\n");
        return 1;
    }
    
    // Verify constraints
    printf("  Verifying gate constraints...");
    if (verify_gate_constraints(witness, 1ULL << num_vars) == 0) {
        printf(" ✓ VALID\n");
    } else {
        printf(" ✗ INVALID\n");
    }
    
    // Generate proof
    printf("  Generating proof...\n");
    basefold_raa_config_t config = {
        .num_variables = num_vars,
        .security_level = 122,
        .enable_zk = 0,  // Disable ZK first to simplify
        .num_threads = 0
    };
    
    basefold_raa_proof_t *proof = malloc(sizeof(basefold_raa_proof_t));
    if (!proof) {
        free(witness);
        return 1;
    }
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    int ret = basefold_raa_prove(witness, &config, proof);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double prove_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    if (ret == 0) {
        printf("    Proof generated in %.3f seconds\n", prove_time);
        
        // Verify proof
        clock_gettime(CLOCK_MONOTONIC, &start);
        ret = basefold_raa_verify(proof, &config);
        clock_gettime(CLOCK_MONOTONIC, &end);
        double verify_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
        printf("  Verification: %s (%.3f ms)\n", 
               ret == 0 ? "PASSED ✓✓✓" : "FAILED ✗",
               verify_time * 1000);
        
        if (ret == 0) {
            printf("\n🎉 SUCCESS! Generated and verified a valid proof!\n\n");
        }
    } else {
        printf("    Proof generation failed: %d\n", ret);
    }
    
    // Cleanup
    free(witness);
    if (proof->sumcheck_commitments) free(proof->sumcheck_commitments);
    if (proof->sumcheck_responses) free(proof->sumcheck_responses);
    if (proof->query_values) free(proof->query_values);
    if (proof->query_indices) free(proof->query_indices);
    if (proof->merkle_paths) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            free(proof->merkle_paths[i]);
        }
        free(proof->merkle_paths);
    }
    if (proof->query_leaf_values) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            free(proof->query_leaf_values[i]);
        }
        free(proof->query_leaf_values);
    }
    free(proof);
    
    // Step 2: Test with multi-gate witness
    printf("Step 2: Testing multi-gate witness\n");
    printf("-----------------------------------\n");
    
    witness = generate_multi_gate_witness(num_vars);
    if (!witness) {
        printf("Failed to generate multi-gate witness\n");
        return 1;
    }
    
    // Verify constraints
    printf("  Verifying gate constraints...");
    if (verify_gate_constraints(witness, 1ULL << num_vars) == 0) {
        printf(" ✓ VALID\n");
    } else {
        printf(" ✗ INVALID\n");
    }
    
    // Generate proof with ZK enabled
    config.enable_zk = 1;
    proof = malloc(sizeof(basefold_raa_proof_t));
    if (!proof) {
        free(witness);
        return 1;
    }
    
    printf("  Generating proof with zero-knowledge...\n");
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    ret = basefold_raa_prove(witness, &config, proof);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    prove_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    if (ret == 0) {
        printf("    Proof generated in %.3f seconds\n", prove_time);
        
        // Verify proof
        clock_gettime(CLOCK_MONOTONIC, &start);
        ret = basefold_raa_verify(proof, &config);
        clock_gettime(CLOCK_MONOTONIC, &end);
        double verify_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
        printf("  Verification: %s (%.3f ms)\n", 
               ret == 0 ? "PASSED ✓✓✓" : "FAILED ✗",
               verify_time * 1000);
        
        if (ret == 0) {
            printf("\n🎉 SUCCESS! Zero-knowledge proof verified!\n");
            printf("This proves we can generate valid proofs for gate circuits.\n");
            printf("Next step: Create state transition circuits for blockchain.\n");
        }
    } else {
        printf("    Proof generation failed: %d\n", ret);
    }
    
    // Cleanup
    free(witness);
    if (proof->sumcheck_commitments) free(proof->sumcheck_commitments);
    if (proof->sumcheck_responses) free(proof->sumcheck_responses);
    if (proof->query_values) free(proof->query_values);
    if (proof->query_indices) free(proof->query_indices);
    if (proof->merkle_paths) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            free(proof->merkle_paths[i]);
        }
        free(proof->merkle_paths);
    }
    if (proof->query_leaf_values) {
        for (size_t i = 0; i < proof->num_queries; i++) {
            free(proof->query_leaf_values[i]);
        }
        free(proof->query_leaf_values);
    }
    free(proof);
    
    return 0;
}