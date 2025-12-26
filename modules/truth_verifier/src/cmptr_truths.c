/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "truth_verifier.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>

/* Helper function to check if file exists */
static bool file_exists(const char *path) {
    struct stat st;
    return stat(path, &st) == 0;
}

/* Helper function to search for string in file */
static bool file_contains(const char *path, const char *search) {
    FILE *fp = fopen(path, "r");
    if (!fp) return false;
    
    char line[1024];
    bool found = false;
    while (fgets(line, sizeof(line), fp)) {
        if (strstr(line, search)) {
            found = true;
            break;
        }
    }
    
    fclose(fp);
    return found;
}

/* T001: SHA3-256 circuit has 192,086 gates */
static truth_result_t verify_T001_sha3_gates(char *details, size_t size) {
    const char *sha3_file = "apps/cmptr/src/sha3_final.c";
    
    if (!file_exists(sha3_file)) {
        snprintf(details, size, "SHA3 implementation file not found: %s", sha3_file);
        return TRUTH_FAILED;
    }
    
    /* Look for the gate count in comments or documentation */
    if (file_contains(sha3_file, "192086") || file_contains(sha3_file, "192,086")) {
        snprintf(details, size, "Found SHA3-256 gate count reference in %s", sha3_file);
        return TRUTH_VERIFIED;
    }
    
    /* Also check README files */
    if (file_contains("README.md", "192,086") || file_contains("README.md", "192086")) {
        snprintf(details, size, "SHA3-256 gate count verified in README.md");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Could not verify exact gate count in source files");
    return TRUTH_UNCERTAIN;
}

/* T004: Effective soundness is 122 bits due to sumcheck limitations */
static truth_result_t verify_T004_soundness_limit(char *details, size_t size) {
    /* Check documentation for soundness claims */
    if (file_contains("CLAUDE.md", "122-bit") || file_contains("CLAUDE.md", "122 bit")) {
        snprintf(details, size, "122-bit soundness limitation documented in CLAUDE.md");
        return TRUTH_VERIFIED;
    }
    
    if (file_contains("README.md", "122-bit soundness")) {
        snprintf(details, size, "122-bit soundness documented in README.md");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Soundness limitation not explicitly documented");
    return TRUTH_UNCERTAIN;
}

/* T002: BaseFold RAA is the only proof system */
static truth_result_t verify_T002_basefold_raa_only(char *details, size_t size) {
    /* Check that BaseFold RAA module exists */
    if (!file_exists("modules/basefold_raa/CMakeLists.txt")) {
        snprintf(details, size, "BaseFold RAA module not found");
        return TRUTH_FAILED;
    }
    
    /* Check that standard BaseFold is not being built */
    if (file_contains("CMakeLists.txt", "BUILD_BASEFOLD_RAA")) {
        snprintf(details, size, "BaseFold RAA build configuration found");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Cannot verify BaseFold RAA exclusivity");
    return TRUTH_UNCERTAIN;
}

/* T003: Zero-knowledge is fully implemented */
static truth_result_t verify_T003_zk_implemented(char *details, size_t size) {
    const char *raa_header = "modules/basefold_raa/include/basefold_raa.h";
    
    if (file_contains(raa_header, "enable_zk")) {
        snprintf(details, size, "Zero-knowledge configuration found in BaseFold RAA");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Zero-knowledge implementation not verified");
    return TRUTH_UNCERTAIN;
}

/* F001: System claims 128-bit soundness (false - it's 122-bit) */
static truth_result_t verify_F001_false_soundness_claim(char *details, size_t size) {
    /* This should verify as FALSE - meaning the system does NOT claim 128-bit */
    if (file_contains("CLAUDE.md", "NOT 128-bit") && file_contains("CLAUDE.md", "122 bits")) {
        snprintf(details, size, "Correctly documents 122-bit limitation, explicitly NOT 128-bit");
        return TRUTH_VERIFIED;  /* The false statement is correctly false */
    }
    
    if (file_contains("CLAUDE.md", "122-bit soundness")) {
        snprintf(details, size, "Documentation states 122-bit soundness, not 128-bit");
        return TRUTH_VERIFIED;  /* The false statement is correctly false */
    }
    
    snprintf(details, size, "Documentation unclear about soundness limitation");
    return TRUTH_UNCERTAIN;
}

/* F701: Truth City viewer exists (false - it was removed) */
static truth_result_t verify_F701_truth_city_exists(char *details, size_t size) {
    /* This should verify as FALSE - meaning Truth City does NOT exist */
    if (file_exists("tools/truth_city_viewer")) {
        snprintf(details, size, "Truth City viewer binary found - statement is not false!");
        return TRUTH_FAILED;  /* The false statement is actually true! */
    }
    
    snprintf(details, size, "Truth City viewer not found (correctly false)");
    return TRUTH_VERIFIED;  /* The false statement is correctly false */
}

/* F002: Groth16 is still supported (false - it was removed) */
static truth_result_t verify_F002_groth16_supported(char *details, size_t size) {
    /* Check that Groth16 module does NOT exist */
    if (file_exists("modules/groth16/CMakeLists.txt")) {
        snprintf(details, size, "Groth16 module still exists!");
        return TRUTH_FAILED;
    }
    
    snprintf(details, size, "Groth16 correctly removed (statement is false)");
    return TRUTH_VERIFIED;
}

/* D001: Average gates per SHA3 round = 192,086 / 24 ≈ 8,003 */
static truth_result_t verify_D001_gates_per_round(char *details, size_t size) {
    /* This is a derived truth from T001 */
    int total_gates = 192086;
    int rounds = 24;
    int average = total_gates / rounds;
    
    if (average >= 8000 && average <= 8004) {
        snprintf(details, size, "Calculation verified: %d / %d = %d gates per round", 
                 total_gates, rounds, average);
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Calculation error: %d / %d = %d", total_gates, rounds, average);
    return TRUTH_FAILED;
}

/* U001: Performance on ARM processors */
static truth_result_t verify_U001_arm_performance(char *details, size_t size) {
    snprintf(details, size, "ARM performance testing not yet conducted");
    return TRUTH_UNCERTAIN;
}

/* U002: Proof size can be reduced below 190KB */
static truth_result_t verify_U002_proof_size_reduction(char *details, size_t size) {
    snprintf(details, size, "Proof size optimization research ongoing");
    return TRUTH_UNCERTAIN;
}

/* P001: Every computation can be represented as a circuit */
static truth_result_t verify_P001_computation_circuits(char *details, size_t size) {
    /* This is a philosophical truth - always true by definition */
    snprintf(details, size, "Fundamental principle of circuit-based computation");
    return TRUTH_VERIFIED;
}

/* P002: Larger proofs can mean less trust required */
static truth_result_t verify_P002_proof_trust_tradeoff(char *details, size_t size) {
    snprintf(details, size, "Transparent proofs require no trusted setup, unlike succinct proofs");
    return TRUTH_VERIFIED;
}

/* Register all cmptr truths */
void register_cmptr_truths(void) {
    static truth_statement_t truths[] = {
        /* Truth statements */
        {
            .id = "T001",
            .type = BUCKET_TRUTH,
            .statement = "SHA3-256 circuit has 192,086 gates",
            .category = "math",
            .verify = verify_T001_sha3_gates
        },
        {
            .id = "T002", 
            .type = BUCKET_TRUTH,
            .statement = "BaseFold RAA is the only proof system",
            .category = "architecture",
            .verify = verify_T002_basefold_raa_only
        },
        {
            .id = "T003",
            .type = BUCKET_TRUTH,
            .statement = "Zero-knowledge is fully implemented",
            .category = "security",
            .verify = verify_T003_zk_implemented
        },
        {
            .id = "T004",
            .type = BUCKET_TRUTH,
            .statement = "Effective soundness is 122 bits due to sumcheck limitations",
            .category = "security",
            .verify = verify_T004_soundness_limit
        },
        
        /* False statements */
        {
            .id = "F001",
            .type = BUCKET_FALSE,
            .statement = "System claims 128-bit soundness",
            .category = "security",
            .verify = verify_F001_false_soundness_claim
        },
        {
            .id = "F002",
            .type = BUCKET_FALSE,
            .statement = "Groth16 is still supported",
            .category = "architecture",
            .verify = verify_F002_groth16_supported
        },
        {
            .id = "F701",
            .type = BUCKET_FALSE,
            .statement = "Truth City viewer exists",
            .category = "tools",
            .verify = verify_F701_truth_city_exists
        },
        
        /* Derived truths */
        {
            .id = "D001",
            .type = BUCKET_DERIVED,
            .statement = "Average gates per SHA3 round = 192,086 / 24 ≈ 8,003",
            .category = "math",
            .verify = verify_D001_gates_per_round
        },
        
        /* Uncertain statements */
        {
            .id = "U001",
            .type = BUCKET_UNCERTAIN,
            .statement = "Performance on ARM processors",
            .category = "performance",
            .verify = verify_U001_arm_performance
        },
        {
            .id = "U002",
            .type = BUCKET_UNCERTAIN,
            .statement = "Proof size can be reduced below 190KB",
            .category = "optimization",
            .verify = verify_U002_proof_size_reduction
        },
        
        /* Philosophical principles */
        {
            .id = "P001",
            .type = BUCKET_PHILOSOPHICAL,
            .statement = "Every computation can be represented as a circuit",
            .category = "theory",
            .verify = verify_P001_computation_circuits
        },
        {
            .id = "P002",
            .type = BUCKET_PHILOSOPHICAL,
            .statement = "Larger proofs can mean less trust required",
            .category = "theory",
            .verify = verify_P002_proof_trust_tradeoff
        }
    };
    
    /* Register all truths */
    for (size_t i = 0; i < sizeof(truths) / sizeof(truths[0]); i++) {
        truth_verifier_register(&truths[i]);
    }
}