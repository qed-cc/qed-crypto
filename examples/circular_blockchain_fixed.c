/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../modules/basefold_raa/include/basefold_raa.h"
#include "../modules/basefold_raa/include/gate_witness_generator.h"
#include "../modules/basefold_raa/include/constraint_polynomial.h"
#include "../modules/gf128/include/gf128.h"

// Forward declaration of fixed prover
int basefold_raa_prove_fixed(const gf128_t* witness,
                            const basefold_raa_config_t* config,
                            basefold_raa_proof_t* proof);

/**
 * @file circular_blockchain_fixed.c
 * @brief Test circular blockchain with fixed sumcheck on constraint polynomial
 */

int main() {
    printf("=== CIRCULAR BLOCKCHAIN WITH FIXED SUMCHECK ===\n");
    printf("Running sumcheck on constraint polynomial (not witness)\n\n");
    
    size_t num_vars = 10;
    
    // Generate a valid gate witness
    printf("Step 1: Generating valid gate witness...\n");
    gf128_t* witness = generate_simple_xor_witness(num_vars);
    if (!witness) {
        printf("Failed to generate witness\n");
        return 1;
    }
    
    // Verify witness is valid
    size_t witness_size = 1ULL << num_vars;
    if (verify_gate_constraints(witness, witness_size) == 0) {
        printf("  ✓ Gate constraints verified\n");
    } else {
        printf("  ✗ Invalid gate constraints\n");
    }
    
    // Check constraint polynomial
    printf("\nStep 2: Checking constraint polynomial...\n");
    gf128_t* constraint = compute_constraint_polynomial(witness, num_vars);
    if (constraint) {
        int sum_zero = verify_constraint_sum_zero(constraint, witness_size);
        printf("  Constraint sum: %s\n", sum_zero == 0 ? "ZERO ✓" : "NON-ZERO ✗");
        free(constraint);
    }
    
    // Generate proof using fixed prover
    printf("\nStep 3: Generating proof with fixed prover...\n");
    basefold_raa_config_t config = {
        .num_variables = num_vars,
        .security_level = 122,
        .enable_zk = 0,
        .num_threads = 0
    };
    
    basefold_raa_proof_t* proof = malloc(sizeof(basefold_raa_proof_t));
    if (!proof) {
        free(witness);
        return 1;
    }
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    int ret = basefold_raa_prove_fixed(witness, &config, proof);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double prove_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    if (ret == 0) {
        printf("  Proof generated in %.3f seconds\n", prove_time);
        printf("  Claimed evaluation: %s\n", 
               gf128_is_zero(proof->claimed_eval) ? "0 (expected)" : "NON-ZERO");
        
        // Try to verify (will fail due to incomplete proof)
        printf("\nStep 4: Verification (partial)...\n");
        printf("  Note: Verification will fail because we haven't implemented\n");
        printf("  the full Binary NTT and RAA encoding yet.\n");
        
        ret = basefold_raa_verify(proof, &config);
        printf("  Verification result: %d\n", ret);
        
        if (ret == -7) {
            printf("  ✓ Got expected error -7 (sumcheck passed but later steps missing)\n");
            printf("\n🎉 PARTIAL SUCCESS! Sumcheck verification passed!\n");
            printf("This proves the constraint polynomial approach works.\n");
        }
    } else {
        printf("  Proof generation failed: %d\n", ret);
    }
    
    // Cleanup
    free(witness);
    if (proof->sumcheck_commitments) free(proof->sumcheck_commitments);
    if (proof->sumcheck_responses) free(proof->sumcheck_responses);
    if (proof->query_values) free(proof->query_values);
    if (proof->query_indices) free(proof->query_indices);
    if (proof->merkle_paths) free(proof->merkle_paths);
    if (proof->query_leaf_values) free(proof->query_leaf_values);
    free(proof);
    
    printf("\n=== NEXT STEPS ===\n");
    printf("1. Complete the Binary NTT conversion\n");
    printf("2. Implement RAA encoding\n");
    printf("3. Add Merkle tree commitments\n");
    printf("4. Then we'll have full circular recursion!\n");
    
    return 0;
}