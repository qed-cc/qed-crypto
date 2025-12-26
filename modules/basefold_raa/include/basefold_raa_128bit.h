/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef BASEFOLD_RAA_128BIT_H
#define BASEFOLD_RAA_128BIT_H

#include <stdint.h>
#include <stddef.h>
#include "gf128.h"

// Configuration for true 128-bit soundness
#define BASEFOLD_RAA_128BIT_QUERIES 320
#define BASEFOLD_RAA_128BIT_SUMCHECK_INSTANCES 2  // For composition

// Enhanced configuration with 128-bit security
typedef struct {
    size_t num_variables;
    size_t security_level;
    int enable_zk;
    int num_threads;
    int enable_sumcheck_composition;  // New: for true 128+ bits
    size_t num_queries;              // Override default
} basefold_raa_config_128bit_t;

// Detailed timing breakdown
typedef struct {
    // Witness processing
    double witness_gen_ms;
    double witness_commit_ms;
    
    // Sumcheck components
    double sumcheck_round_ms[18];    // Per-round timing
    double sumcheck_total_ms;
    double sumcheck_compose_ms;       // Composition overhead
    
    // Polynomial operations
    double binary_ntt_ms;
    double multilinear_eval_ms;
    double polynomial_commit_ms;
    
    // RAA encoding
    double raa_repeat_ms;
    double raa_permute1_ms;
    double raa_accumulate1_ms;
    double raa_permute2_ms;
    double raa_accumulate2_ms;
    double raa_total_ms;
    
    // Merkle tree
    double merkle_leaf_hash_ms;
    double merkle_tree_build_ms;
    double merkle_root_ms;
    double merkle_total_ms;
    
    // Query phase
    double query_sample_ms;
    double query_open_ms;
    double query_path_ms;
    double query_total_ms;
    
    // Totals
    double prove_total_ms;
    double verify_total_ms;
    
    // Verification breakdown
    double verify_sumcheck_ms;
    double verify_polynomial_ms;
    double verify_raa_ms;
    double verify_queries_ms;
    
    // Sizes
    size_t proof_size_bytes;
    size_t witness_size;
    size_t codeword_size;
    
    // CPU cycles (for detailed analysis)
    uint64_t total_cycles;
    uint64_t gf128_mul_cycles;
    uint64_t gf128_add_cycles;
    uint64_t sha3_cycles;
} basefold_timing_breakdown_t;

// Enhanced proof structure with composition
typedef struct {
    // Sumcheck composition proofs
    uint8_t sumcheck_commits[2][18][32];      // 2 instances, 18 rounds
    gf128_t sumcheck_responses[2][18][3];     // g(0), g(1), g(2) for each
    uint8_t composition_commit[32];           // Commitment to composition
    
    // RAA components
    uint8_t raa_root[32];
    gf128_t final_eval;
    
    // Query responses
    size_t num_queries;
    uint32_t* query_positions;
    gf128_t* query_values;
    uint8_t (*query_paths)[18][32];  // Merkle authentication paths
    
    // Metadata
    size_t num_variables;
    int composition_used;
} basefold_raa_proof_128bit_t;

// Main API for 128-bit security
int basefold_raa_prove_128bit(
    const gf128_t* witness,
    const basefold_raa_config_128bit_t* config,
    basefold_raa_proof_128bit_t* proof,
    basefold_timing_breakdown_t* timing
);

int basefold_raa_verify_128bit(
    const basefold_raa_proof_128bit_t* proof,
    const basefold_raa_config_128bit_t* config,
    basefold_timing_breakdown_t* timing
);

// Utility functions
size_t basefold_raa_proof_size_128bit(const basefold_raa_config_128bit_t* config);
void basefold_raa_proof_free_128bit(basefold_raa_proof_128bit_t* proof);
void basefold_timing_print_report(const basefold_timing_breakdown_t* timing);

#endif // BASEFOLD_RAA_128BIT_H