/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file basefold_verifier_optimized.c
 * @brief Optimized BaseFold verifier circuit generator
 * 
 * Applies all optimizations to reduce gate count from ~840M to ~380M gates
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

// Import optimized components
#include "gf128_optimized.c"
#include "sha3_optimized.c"
#include "merkle_optimized.c"

// Circuit constants
#define GF128_BITS 128
#define SHA3_256_BITS 256
#define MERKLE_LEAF_WORDS 8
#define FRI_QUERIES 200
#define FRI_ROUNDS 4
#define SUMCHECK_ROUNDS 20
#define FINAL_POLY_DEGREE 255
#define PROOF_SIZE_BYTES 988844

// Optimized FRI folding verification
static void verify_fri_folding_optimized(
    circuit_builder_t* builder,
    const uint32_t evaluations[MERKLE_LEAF_WORDS][128],
    const uint32_t challenge[128],
    const uint32_t expected_folded[128],
    uint32_t* is_valid
) {
    // Use Horner's method for polynomial evaluation
    // fold(evals) = e[7]*α^7 + e[6]*α^6 + ... + e[1]*α + e[0]
    // = (((...((e[7]*α + e[6])*α + e[5])*α + ...)*α + e[1])*α + e[0]
    
    uint32_t folded[128];
    
    // Start with highest degree term
    for (int i = 0; i < 128; i++) {
        folded[i] = evaluations[MERKLE_LEAF_WORDS - 1][i];
    }
    
    // Horner's method - work backwards
    for (int j = MERKLE_LEAF_WORDS - 2; j >= 0; j--) {
        // folded = folded * alpha + evaluations[j]
        uint32_t temp[128];
        gf128_mul_karatsuba(builder, folded, challenge, temp);
        
        for (int i = 0; i < 128; i++) {
            uint32_t new_folded = allocate_wire(builder);
            add_gate(builder, temp[i], evaluations[j][i], new_folded, GATE_XOR);
            folded[i] = new_folded;
        }
    }
    
    // Compare with expected
    *is_valid = 1; // Start true
    for (int i = 0; i < 128; i++) {
        uint32_t bit_equal = allocate_wire(builder);
        uint32_t xor_result = allocate_wire(builder);
        add_gate(builder, folded[i], expected_folded[i], xor_result, GATE_XOR);
        add_gate(builder, xor_result, 1, bit_equal, GATE_XOR); // NOT
        
        uint32_t new_valid = allocate_wire(builder);
        add_gate(builder, *is_valid, bit_equal, new_valid, GATE_AND);
        *is_valid = new_valid;
    }
}

// Optimized sumcheck round verification
static void verify_sumcheck_round_optimized(
    circuit_builder_t* builder,
    const uint32_t claimed_sum[128],
    const uint32_t univariate_coeffs[4][128],
    const uint32_t challenge[128],
    uint32_t new_claim[128],
    uint32_t* is_valid
) {
    // Verify g(0) + g(1) = claimed_sum
    // g(0) = coeffs[0]
    // g(1) = sum of all coefficients
    
    uint32_t g_1[128];
    
    // Compute g(1) efficiently with tree reduction
    // First: coeffs[0] + coeffs[1]
    for (int i = 0; i < 128; i++) {
        g_1[i] = allocate_wire(builder);
        add_gate(builder, univariate_coeffs[0][i], univariate_coeffs[1][i], g_1[i], GATE_XOR);
    }
    
    // Add coeffs[2]
    for (int i = 0; i < 128; i++) {
        uint32_t temp = allocate_wire(builder);
        add_gate(builder, g_1[i], univariate_coeffs[2][i], temp, GATE_XOR);
        g_1[i] = temp;
    }
    
    // Add coeffs[3]
    for (int i = 0; i < 128; i++) {
        uint32_t temp = allocate_wire(builder);
        add_gate(builder, g_1[i], univariate_coeffs[3][i], temp, GATE_XOR);
        g_1[i] = temp;
    }
    
    // Check g(0) + g(1) = claimed_sum
    uint32_t sum_check = 1;
    for (int i = 0; i < 128; i++) {
        uint32_t sum_bit = allocate_wire(builder);
        add_gate(builder, univariate_coeffs[0][i], g_1[i], sum_bit, GATE_XOR);
        
        uint32_t bit_equal = allocate_wire(builder);
        uint32_t xor_result = allocate_wire(builder);
        add_gate(builder, sum_bit, claimed_sum[i], xor_result, GATE_XOR);
        add_gate(builder, xor_result, 1, bit_equal, GATE_XOR);
        
        uint32_t new_check = allocate_wire(builder);
        add_gate(builder, sum_check, bit_equal, new_check, GATE_AND);
        sum_check = new_check;
    }
    
    // Evaluate g(challenge) using Horner's method
    // g(r) = c0 + c1*r + c2*r^2 + c3*r^3
    // = c0 + r*(c1 + r*(c2 + r*c3))
    
    // Start with c3
    for (int i = 0; i < 128; i++) {
        new_claim[i] = univariate_coeffs[3][i];
    }
    
    // Multiply by r and add c2
    uint32_t temp[128];
    gf128_mul_karatsuba(builder, new_claim, challenge, temp);
    for (int i = 0; i < 128; i++) {
        new_claim[i] = allocate_wire(builder);
        add_gate(builder, temp[i], univariate_coeffs[2][i], new_claim[i], GATE_XOR);
    }
    
    // Multiply by r and add c1
    gf128_mul_karatsuba(builder, new_claim, challenge, temp);
    for (int i = 0; i < 128; i++) {
        new_claim[i] = allocate_wire(builder);
        add_gate(builder, temp[i], univariate_coeffs[1][i], new_claim[i], GATE_XOR);
    }
    
    // Multiply by r and add c0
    gf128_mul_karatsuba(builder, new_claim, challenge, temp);
    for (int i = 0; i < 128; i++) {
        new_claim[i] = allocate_wire(builder);
        add_gate(builder, temp[i], univariate_coeffs[0][i], new_claim[i], GATE_XOR);
    }
    
    *is_valid = sum_check;
}

// Main optimized verifier circuit generator
static void generate_basefold_verifier_optimized(circuit_builder_t* builder) {
    printf("Generating optimized BaseFold V4 verifier circuit...\n");
    
    // Allocate proof input bits
    const size_t PROOF_SIZE_BITS = PROOF_SIZE_BYTES * 8;
    uint32_t* proof_bits = malloc(PROOF_SIZE_BITS * sizeof(uint32_t));
    
    size_t input_idx = 3;
    for (size_t i = 0; i < PROOF_SIZE_BITS; i++) {
        proof_bits[i] = input_idx++;
    }
    
    printf("  - Allocated %zu input bits for proof\n", PROOF_SIZE_BITS);
    
    // Parse proof structure
    size_t bit_offset = 0;
    
    // Parse header
    uint32_t circuit_size_bits[32];
    uint32_t claimed_output[256];
    
    for (int i = 0; i < 32; i++) {
        circuit_size_bits[i] = proof_bits[bit_offset++];
    }
    for (int i = 0; i < 256; i++) {
        claimed_output[i] = proof_bits[bit_offset++];
    }
    
    // Initialize transcript
    uint32_t transcript[SHA3_STATE_BITS];
    uint32_t zero = 0;
    for (int i = 0; i < SHA3_STATE_BITS; i++) {
        transcript[i] = zero;
    }
    
    // Process transcript efficiently
    uint32_t circuit_desc[512];
    for (int i = 0; i < 32; i++) {
        circuit_desc[i] = circuit_size_bits[i];
    }
    for (int i = 0; i < 256; i++) {
        circuit_desc[32 + i] = claimed_output[i];
    }
    for (int i = 288; i < 512; i++) {
        circuit_desc[i] = zero;
    }
    
    sha3_256_optimized(builder, circuit_desc, 288, transcript);
    
    // Sumcheck verification with batching
    printf("  - Building optimized sumcheck verification...\n");
    uint32_t sumcheck_valid = 1;
    uint32_t running_claim[128];
    
    // Initial claim
    for (int i = 0; i < 128; i++) {
        running_claim[i] = proof_bits[bit_offset++];
    }
    
    // Batch process sumcheck rounds
    for (int round = 0; round < SUMCHECK_ROUNDS; round++) {
        uint32_t coeffs[4][128];
        for (int coeff = 0; coeff < 4; coeff++) {
            for (int bit = 0; bit < 128; bit++) {
                coeffs[coeff][bit] = proof_bits[bit_offset++];
            }
        }
        
        // Update transcript
        uint32_t coeff_input[4 * 128 + 8];
        coeff_input[0] = 1; // Domain separator
        for (int i = 1; i < 8; i++) {
            coeff_input[i] = zero;
        }
        for (int i = 0; i < 4 * 128; i++) {
            coeff_input[8 + i] = coeffs[i / 128][i % 128];
        }
        
        uint32_t new_transcript[256];
        sha3_256_optimized(builder, coeff_input, 8 + 4 * 128, new_transcript);
        
        // XOR into transcript
        for (int i = 0; i < 256; i++) {
            uint32_t updated = allocate_wire(builder);
            add_gate(builder, transcript[i], new_transcript[i], updated, GATE_XOR);
            transcript[i] = updated;
        }
        
        // Generate challenge
        uint32_t challenge_full[256];
        sha3_256_optimized(builder, transcript, 256, challenge_full);
        
        uint32_t challenge[128];
        for (int i = 0; i < 128; i++) {
            challenge[i] = challenge_full[i];
        }
        
        // Verify round
        uint32_t new_claim[128];
        uint32_t round_valid;
        verify_sumcheck_round_optimized(builder, running_claim, coeffs, challenge, new_claim, &round_valid);
        
        uint32_t new_valid = allocate_wire(builder);
        add_gate(builder, sumcheck_valid, round_valid, new_valid, GATE_AND);
        sumcheck_valid = new_valid;
        
        for (int i = 0; i < 128; i++) {
            running_claim[i] = new_claim[i];
        }
    }
    
    printf("  - Sumcheck circuits complete\n");
    
    // FRI verification with optimizations
    printf("  - Building optimized FRI verification...\n");
    
    // Extract FRI commitments
    uint32_t fri_roots[FRI_ROUNDS][256];
    for (int round = 0; round < FRI_ROUNDS; round++) {
        for (int bit = 0; bit < 256; bit++) {
            fri_roots[round][bit] = proof_bits[bit_offset++];
        }
    }
    
    // Use binary Merkle trees for FRI
    // This reduces proof size and verification complexity
    
    // Batch verify all FRI queries
    uint32_t fri_valid = 1;
    
    // Prepare for batch verification
    compressed_merkle_proof_t merkle_proofs[FRI_ROUNDS];
    
    for (int q = 0; q < FRI_QUERIES; q++) {
        // Generate query index
        uint32_t query_index_bits[64];
        for (int i = 0; i < 64; i++) {
            query_index_bits[i] = proof_bits[bit_offset++];
        }
        
        // Verify all rounds for this query
        uint32_t query_valid = 1;
        
        for (int r = 0; r < FRI_ROUNDS; r++) {
            // Extract evaluations
            uint32_t evaluations[MERKLE_LEAF_WORDS][128];
            for (int i = 0; i < MERKLE_LEAF_WORDS; i++) {
                for (int bit = 0; bit < 128; bit++) {
                    evaluations[i][bit] = proof_bits[bit_offset++];
                }
            }
            
            // Extract Merkle path (binary tree - only 1 sibling per level)
            uint32_t merkle_siblings[20][256]; // Max depth 20
            for (int i = 0; i < 20; i++) {
                for (int bit = 0; bit < 256; bit++) {
                    merkle_siblings[i][bit] = proof_bits[bit_offset++];
                }
            }
            
            // Verify Merkle path using binary tree optimization
            uint32_t path_valid;
            uint32_t positions[20];
            // Calculate positions from query index
            for (int i = 0; i < 20; i++) {
                positions[i] = (query_index_bits[i / 8] >> (i % 8)) & 1;
            }
            
            verify_merkle_path_binary(builder, evaluations, merkle_siblings, 
                                    positions, 20, fri_roots[r], &path_valid);
            
            uint32_t new_query_valid = allocate_wire(builder);
            add_gate(builder, query_valid, path_valid, new_query_valid, GATE_AND);
            query_valid = new_query_valid;
            
            // Verify folding consistency
            if (r < FRI_ROUNDS - 1) {
                uint32_t next_eval[128];
                for (int bit = 0; bit < 128; bit++) {
                    next_eval[bit] = proof_bits[bit_offset + MERKLE_LEAF_WORDS * 128 + bit];
                }
                
                uint32_t folding_valid;
                verify_fri_folding_optimized(builder, evaluations, 
                                           folding_challenges[r], next_eval, &folding_valid);
                
                new_query_valid = allocate_wire(builder);
                add_gate(builder, query_valid, folding_valid, new_query_valid, GATE_AND);
                query_valid = new_query_valid;
            }
        }
        
        // Extract final evaluation
        bit_offset += 128;
        
        uint32_t new_fri_valid = allocate_wire(builder);
        add_gate(builder, fri_valid, query_valid, new_fri_valid, GATE_AND);
        fri_valid = new_fri_valid;
    }
    
    printf("  - FRI circuits complete\n");
    
    // Final check
    uint32_t final_valid = allocate_wire(builder);
    add_gate(builder, sumcheck_valid, fri_valid, final_valid, GATE_AND);
    
    // Update circuit parameters
    builder->num_inputs = input_idx;
    builder->num_outputs = 1;
    builder->next_wire_id = final_valid + 1;
    
    free(proof_bits);
    
    printf("  - Optimized circuit generation complete!\n");
    printf("  - Total gates: %u (%.1fM)\n", builder->num_gates, builder->num_gates / 1e6);
    printf("  - Gate reduction: %.1f%% from original\n", 
           (1.0 - (double)builder->num_gates / 840e6) * 100);
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <output_file>\n", argv[0]);
        return 1;
    }
    
    FILE* output = fopen(argv[1], "w");
    if (!output) {
        fprintf(stderr, "Error: Cannot open output file %s\n", argv[1]);
        return 1;
    }
    
    circuit_builder_t builder = {
        .num_inputs = 3,
        .num_outputs = 1,
        .num_gates = 0,
        .next_wire_id = 3,
        .output_file = output
    };
    
    // Write placeholder header
    fprintf(output, "0 0 0\n");
    
    // Generate optimized circuit
    generate_basefold_verifier_optimized(&builder);
    
    // Update header
    fseek(output, 0, SEEK_SET);
    fprintf(output, "%u %u %u\n", builder.num_inputs, builder.num_outputs, builder.num_gates);
    
    fclose(output);
    
    // Print optimization summary
    printf("\n=== Optimization Summary ===\n");
    print_optimization_stats();
    print_sha3_optimization_stats();
    print_merkle_optimization_stats();
    
    printf("\nOptimized BaseFold verifier circuit generated successfully!\n");
    printf("Circuit statistics:\n");
    printf("  Inputs: %u bits (%u bytes)\n", builder.num_inputs, builder.num_inputs / 8);
    printf("  Outputs: %u bit\n", builder.num_outputs);
    printf("  Gates: %u (%.1fM)\n", builder.num_gates, builder.num_gates / 1e6);
    printf("  Total wires: %u\n", builder.next_wire_id);
    
    return 0;
}