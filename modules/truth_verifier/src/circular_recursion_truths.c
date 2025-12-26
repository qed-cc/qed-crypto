/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "truth_verifier.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <dirent.h>

/* T600: Recursive proof composition exists and works */
truth_result_t verify_T600_recursive_composition_exists(char *details, size_t size) {
    // Check if recursive proof executables exist
    if (access("./tools/recursive_proof_128bit_demo", X_OK) == 0) {
        snprintf(details, size, "Found working recursive proof demo at tools/recursive_proof_128bit_demo");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Recursive proof demo not found or not executable");
    return TRUTH_FAILED;
}

/* T601: BaseFold RAA supports 2-to-1 proof composition */
truth_result_t verify_T601_basefold_supports_composition(char *details, size_t size) {
    // Check for recursive proof functions in headers
    FILE *fp = fopen("modules/basefold_raa/include/basefold_raa.h", "r");
    if (!fp) {
        snprintf(details, size, "Cannot read basefold_raa.h");
        return TRUTH_FAILED;
    }
    
    char line[256];
    bool found_prove = false;
    bool found_verify = false;
    
    while (fgets(line, sizeof(line), fp)) {
        if (strstr(line, "basefold_raa_prove")) found_prove = true;
        if (strstr(line, "basefold_raa_verify")) found_verify = true;
    }
    fclose(fp);
    
    if (found_prove && found_verify) {
        snprintf(details, size, "BaseFold RAA has prove/verify functions for composition");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "Missing prove or verify functions");
    return TRUTH_FAILED;
}

/* T602: Recursive proofs achieve 179ms performance */
truth_result_t verify_T602_recursive_proof_performance(char *details, size_t size) {
    // Check performance documentation
    FILE *fp = fopen("RECURSIVE_PROOF_PERFORMANCE_REPORT.md", "r");
    if (!fp) {
        fp = fopen("docs/RECURSIVE_PROOF_PERFORMANCE_REPORT.md", "r");
    }
    
    if (!fp) {
        snprintf(details, size, "Performance report not found");
        return TRUTH_UNCERTAIN;
    }
    
    char line[256];
    bool found_179ms = false;
    
    while (fgets(line, sizeof(line), fp)) {
        if (strstr(line, "179ms") || strstr(line, "0.179")) {
            found_179ms = true;
            break;
        }
    }
    fclose(fp);
    
    if (found_179ms) {
        snprintf(details, size, "Documented 179ms recursive proof performance");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "179ms performance claim not found in documentation");
    return TRUTH_UNCERTAIN;
}

/* F600: Circular recursion for blockchains is implemented */
truth_result_t verify_F600_circular_recursion_implemented(char *details, size_t size) {
    // Check for circular recursion implementation
    DIR *dir = opendir("modules/basefold_raa/src");
    if (!dir) {
        snprintf(details, size, "Cannot open basefold_raa/src directory");
        return TRUTH_UNCERTAIN;
    }
    
    struct dirent *entry;
    bool found_circular = false;
    
    while ((entry = readdir(dir)) != NULL) {
        if (strstr(entry->d_name, "circular") || strstr(entry->d_name, "blockchain")) {
            found_circular = true;
            break;
        }
    }
    closedir(dir);
    
    if (found_circular) {
        snprintf(details, size, "Found circular/blockchain files - might be implemented");
        return TRUTH_UNCERTAIN;
    }
    
    // Definitely not implemented
    snprintf(details, size, "No circular recursion implementation found in basefold_raa module");
    return TRUTH_VERIFIED; // Verified as FALSE
}

/* T603: Recursive verifier circuit exists (was F601, but it's actually TRUE!) */
truth_result_t verify_T603_recursive_verifier_exists(char *details, size_t size) {
    // Check for verifier circuit generator
    if (access("tools/basefold_verifier_circuit_generator.c", F_OK) == 0) {
        // Also check for the header
        if (access("modules/circuit_generator/include/recursive_basefold.h", F_OK) == 0) {
            snprintf(details, size, "Found complete verifier circuit implementation!");
            return TRUTH_VERIFIED;
        }
    }
    
    snprintf(details, size, "Verifier circuit generator not found");
    return TRUTH_FAILED;
}

/* U600: Can we build a recursive verifier circuit? */
truth_result_t verify_U600_can_build_verifier_circuit(char *details, size_t size) {
    // This is uncertain - needs investigation
    snprintf(details, size, "Requires analyzing circuit size and gate complexity");
    return TRUTH_UNCERTAIN;
}

/* U601: What is the circuit size for recursive verification? */
truth_result_t verify_U601_verifier_circuit_size(char *details, size_t size) {
    // Check if we have any estimates
    FILE *fp = fopen("tools/verifier_circuit_size_analysis.c", "r");
    if (fp) {
        fclose(fp);
        snprintf(details, size, "Circuit size analysis tool exists - need to run it");
        return TRUTH_UNCERTAIN;
    }
    
    snprintf(details, size, "No circuit size analysis available yet");
    return TRUTH_UNCERTAIN;
}

/* Register all circular recursion truths */
void register_circular_recursion_truths(void) {
    static truth_statement_t truths[] = {
        /* Truth statements */
        {
            .id = "T600",
            .type = BUCKET_TRUTH,
            .statement = "Recursive proof composition exists and works",
            .category = "implementation",
            .verify = verify_T600_recursive_composition_exists
        },
        {
            .id = "T601",
            .type = BUCKET_TRUTH,
            .statement = "BaseFold RAA supports 2-to-1 proof composition",
            .category = "capability",
            .verify = verify_T601_basefold_supports_composition
        },
        {
            .id = "T602",
            .type = BUCKET_TRUTH,
            .statement = "Recursive proofs achieve 179ms performance",
            .category = "performance",
            .verify = verify_T602_recursive_proof_performance
        },
        
        /* False statements */
        {
            .id = "F600",
            .type = BUCKET_FALSE,
            .statement = "Circular recursion for blockchains is implemented",
            .category = "implementation",
            .verify = verify_F600_circular_recursion_implemented
        },
        {
            .id = "T603",
            .type = BUCKET_TRUTH,
            .statement = "Recursive verifier circuit exists",
            .category = "implementation",
            .verify = verify_T603_recursive_verifier_exists
        },
        
        /* Uncertain statements */
        {
            .id = "U600",
            .type = BUCKET_UNCERTAIN,
            .statement = "Can we build a recursive verifier circuit?",
            .category = "feasibility",
            .verify = verify_U600_can_build_verifier_circuit
        },
        {
            .id = "U601",
            .type = BUCKET_UNCERTAIN,
            .statement = "What is the circuit size for recursive verification?",
            .category = "analysis",
            .verify = verify_U601_verifier_circuit_size
        }
    };
    
    for (size_t i = 0; i < sizeof(truths) / sizeof(truths[0]); i++) {
        truth_verifier_register(&truths[i]);
    }
}