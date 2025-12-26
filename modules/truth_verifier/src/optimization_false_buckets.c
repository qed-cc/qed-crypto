/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file optimization_false_buckets.c
 * @brief False buckets - common misconceptions about optimization
 */

#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include "../include/truth_verifier.h"

// FALSE: We can use Poseidon for internal hashing
truth_result_t verify_F010_poseidon_allowed(char *details, size_t size) {
    snprintf(details, size, 
        "FALSE: Poseidon (60K gates) would give 3.3x speedup. "
        "But Axiom A001 forbids ALL hash functions except SHA3. "
        "This applies to every component - no exceptions.");
    
    return TRUTH_FAILED;  // This is FALSE
}

// FALSE: We can use different hash for Fiat-Shamir
truth_result_t verify_F011_different_hash_fiat_shamir(char *details, size_t size) {
    snprintf(details, size, 
        "FALSE: Even for challenge generation, we cannot use SHA2 or Blake3. "
        "Axiom A001 requires SHA3 for ALL hashing in the proof system. "
        "No hybrid approaches allowed.");
    
    return TRUTH_FAILED;  // This is FALSE
}

// FALSE: We can approximate verification
truth_result_t verify_F012_approximate_verification(char *details, size_t size) {
    snprintf(details, size, 
        "FALSE: Cannot verify with 99.9%% confidence instead of 100%%. "
        "Must maintain 122-bit security and complete verification. "
        "Probabilistic shortcuts violate security requirements.");
    
    return TRUTH_FAILED;  // This is FALSE
}

// FALSE: We can go faster than 600ms with SHA3
truth_result_t verify_F013_break_600ms_floor(char *details, size_t size) {
    snprintf(details, size, 
        "FALSE: Memory bandwidth creates hard floor around 600ms. "
        "Must move 8.6GB of data. Even with infinite compute, "
        "DDR5 bandwidth limits us. Physics cannot be violated.");
    
    return TRUTH_FAILED;  // This is FALSE
}

// FALSE: Circuit can be reduced below 250M gates
truth_result_t verify_F014_circuit_below_250M(char *details, size_t size) {
    snprintf(details, size, 
        "FALSE: With SHA3 at 200K gates and 320 queries minimum for security, "
        "Merkle alone needs 64M gates absolute minimum. "
        "Plus other components, 250M gates is the floor.");
    
    return TRUTH_FAILED;  // This is FALSE
}

// Register all false buckets
void register_optimization_false_buckets(void) {
    static truth_statement_t falses[] = {
        {
            .id = "F010",
            .type = BUCKET_FALSE,
            .statement = "We can use Poseidon for internal hashing",
            .category = "optimization",
            .verify = verify_F010_poseidon_allowed
        },
        {
            .id = "F011",
            .type = BUCKET_FALSE,
            .statement = "We can use different hash for Fiat-Shamir",
            .category = "optimization",
            .verify = verify_F011_different_hash_fiat_shamir
        },
        {
            .id = "F012",
            .type = BUCKET_FALSE,
            .statement = "We can approximate verification",
            .category = "optimization",
            .verify = verify_F012_approximate_verification
        },
        {
            .id = "F013",
            .type = BUCKET_FALSE,
            .statement = "We can go faster than 600ms with SHA3",
            .category = "optimization",
            .verify = verify_F013_break_600ms_floor
        },
        {
            .id = "F014",
            .type = BUCKET_FALSE,
            .statement = "Circuit can be reduced below 250M gates",
            .category = "optimization",
            .verify = verify_F014_circuit_below_250M
        }
    };
    
    for (size_t i = 0; i < sizeof(falses) / sizeof(falses[0]); i++) {
        truth_verifier_register(&falses[i]);
    }
}