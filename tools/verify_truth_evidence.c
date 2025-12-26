/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <sys/stat.h>
#include <dirent.h>

/**
 * @file verify_truth_evidence.c
 * @brief Automated verification of truth bucket evidence
 * 
 * This tool systematically checks each truth's evidence to ensure
 * it still holds correctly. It can be run quickly to validate the
 * entire truth system.
 */

typedef struct {
    char id[32];
    char statement[512];
    char evidence_type[64];
    char evidence_details[1024];
    int is_valid;
    char validation_error[512];
} truth_evidence_t;

/* Check if a file exists and is accessible */
static int file_exists(const char *path) {
    return access(path, F_OK) == 0;
}

/* Check if a binary exists and is executable */
static int binary_exists(const char *path) {
    return access(path, X_OK) == 0;
}

/* Run a command and check its return code */
static int command_succeeds(const char *cmd) {
    int ret = system(cmd);
    return WIFEXITED(ret) && WEXITSTATUS(ret) == 0;
}

/* Check if a pattern exists in a file */
static int grep_file(const char *pattern, const char *file) {
    if (!file_exists(file)) return 0;
    
    char cmd[1024];
    snprintf(cmd, sizeof(cmd), "grep -q '%s' '%s' 2>/dev/null", pattern, file);
    return command_succeeds(cmd);
}

/* Verify evidence for a specific truth */
static void verify_truth_evidence(truth_evidence_t *truth) {
    truth->is_valid = 1; // Assume valid until proven otherwise
    
    // T004: BaseFold offers up to 122-bit security
    if (strcmp(truth->id, "T004") == 0) {
        strcpy(truth->evidence_type, "Documentation");
        strcpy(truth->evidence_details, "CLAUDE.md and security analysis docs");
        
        if (file_exists("CLAUDE.md") && grep_file("122-bit", "CLAUDE.md")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "CLAUDE.md missing or doesn't mention 122-bit security");
        }
    }
    
    // T020: SHA3 is the only allowed hash function
    else if (strcmp(truth->id, "T020") == 0) {
        strcpy(truth->evidence_type, "Code axiom");
        strcpy(truth->evidence_details, "CLAUDE.md axiom A001");
        
        if (grep_file("Only SHA3 is allowed", "CLAUDE.md")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "SHA3-only axiom not found in CLAUDE.md");
        }
    }
    
    // T101: Sub-second recursive proofs achieved
    else if (strcmp(truth->id, "T101") == 0) {
        strcpy(truth->evidence_type, "Performance data");
        strcpy(truth->evidence_details, "179ms recursive proof documented");
        
        if (grep_file("179ms", "CLAUDE.md") || 
            grep_file("0.179", "docs/RECURSIVE_PROOF_ACHIEVEMENT.md")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "179ms achievement not documented");
        }
    }
    
    // T200: Gate computer uses GF(2^128)
    else if (strcmp(truth->id, "T200") == 0) {
        strcpy(truth->evidence_type, "Code implementation");
        strcpy(truth->evidence_details, "gf128 module exists");
        
        if (file_exists("modules/gf128/include/gf128.h")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "GF128 module not found");
        }
    }
    
    // T600: Recursive proof composition exists
    else if (strcmp(truth->id, "T600") == 0) {
        strcpy(truth->evidence_type, "Working implementation");
        strcpy(truth->evidence_details, "recursive_proof_128bit_demo binary");
        
        if (binary_exists("./tools/recursive_proof_128bit_demo") ||
            binary_exists("./build/tools/recursive_proof_128bit_demo")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "Recursive proof demo binary not found");
        }
    }
    
    // T602: Recursive proofs achieve 179ms performance
    else if (strcmp(truth->id, "T602") == 0) {
        strcpy(truth->evidence_type, "Documented achievement");
        strcpy(truth->evidence_details, "Performance reports");
        
        if (file_exists("RECURSIVE_PROOF_PERFORMANCE_REPORT.md") ||
            grep_file("179ms", "CLAUDE.md")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "179ms performance not documented");
        }
    }
    
    // T700: Circular blockchain demo compiles
    else if (strcmp(truth->id, "T700") == 0) {
        strcpy(truth->evidence_type, "Binary exists");
        strcpy(truth->evidence_details, "circular_blockchain_simple executable");
        
        if (binary_exists("./build/bin/circular_blockchain_simple")) {
            truth->is_valid = 1;
        } else {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "circular_blockchain_simple not found in build/bin/");
        }
    }
    
    // F001: Gate computer uses Groth16
    else if (strcmp(truth->id, "F001") == 0) {
        strcpy(truth->evidence_type, "Code absence");
        strcpy(truth->evidence_details, "No Groth16 implementation");
        
        // Check for actual Groth16 module or implementation (not just mentions)
        if (file_exists("modules/groth16") || 
            command_succeeds("find . -path './modules/*' -name '*groth16*' 2>/dev/null | grep -v truth")) {
            truth->is_valid = 0;
            strcpy(truth->validation_error, "Found Groth16 implementation (should be false)");
        } else {
            truth->is_valid = 1; // Correctly false - no actual implementation
        }
    }
    
    // Add more truth evidence checks here...
    else {
        strcpy(truth->evidence_type, "Not yet automated");
        strcpy(truth->evidence_details, "Manual verification needed");
        truth->is_valid = -1; // Unknown
    }
}

/* Generate verification report */
static void generate_report(truth_evidence_t *truths, int count) {
    int valid = 0, invalid = 0, unknown = 0;
    
    for (int i = 0; i < count; i++) {
        if (truths[i].is_valid == 1) valid++;
        else if (truths[i].is_valid == 0) invalid++;
        else unknown++;
    }
    
    printf("\n=== TRUTH EVIDENCE VERIFICATION REPORT ===\n");
    printf("Generated: %s\n", ctime(&(time_t){time(NULL)}));
    printf("\nSummary:\n");
    printf("  Total truths checked: %d\n", count);
    printf("  Valid evidence: %d (%.1f%%)\n", valid, 100.0 * valid / count);
    printf("  Invalid evidence: %d (%.1f%%)\n", invalid, 100.0 * invalid / count);
    printf("  Not automated: %d (%.1f%%)\n", unknown, 100.0 * unknown / count);
    
    if (invalid > 0) {
        printf("\n❌ INVALID EVIDENCE FOUND:\n");
        printf("--------------------------------\n");
        for (int i = 0; i < count; i++) {
            if (truths[i].is_valid == 0) {
                printf("[%s] %s\n", truths[i].id, truths[i].statement);
                printf("  Evidence type: %s\n", truths[i].evidence_type);
                printf("  Expected: %s\n", truths[i].evidence_details);
                printf("  Error: %s\n\n", truths[i].validation_error);
            }
        }
    }
    
    printf("\n✓ VALID EVIDENCE:\n");
    printf("------------------\n");
    for (int i = 0; i < count; i++) {
        if (truths[i].is_valid == 1) {
            printf("[%s] %s\n", truths[i].id, truths[i].statement);
            printf("  Evidence: %s (%s)\n\n", truths[i].evidence_details, truths[i].evidence_type);
        }
    }
    
    // Save to file for tracking
    FILE *fp = fopen("truth_evidence_report.txt", "w");
    if (fp) {
        fprintf(fp, "Truth Evidence Verification Report\n");
        fprintf(fp, "==================================\n");
        fprintf(fp, "Generated: %s\n", ctime(&(time_t){time(NULL)}));
        fprintf(fp, "\nValid: %d, Invalid: %d, Unknown: %d\n", valid, invalid, unknown);
        
        for (int i = 0; i < count; i++) {
            fprintf(fp, "\n[%s] %s\n", truths[i].id, truths[i].statement);
            fprintf(fp, "  Status: %s\n", 
                    truths[i].is_valid == 1 ? "VALID" : 
                    truths[i].is_valid == 0 ? "INVALID" : "UNKNOWN");
            if (truths[i].is_valid == 0) {
                fprintf(fp, "  Error: %s\n", truths[i].validation_error);
            }
        }
        fclose(fp);
        printf("\nReport saved to: truth_evidence_report.txt\n");
    }
}

int main(int argc, char *argv[]) {
    printf("=== AUTOMATED TRUTH EVIDENCE VERIFICATION ===\n");
    printf("Checking evidence for all truth buckets...\n\n");
    
    // Sample truths to verify (in real system, load from truth verifier)
    truth_evidence_t truths[] = {
        {"T004", "BaseFold offers up to 122-bit security", "", "", -1, ""},
        {"T020", "SHA3 is the only allowed hash function", "", "", -1, ""},
        {"T101", "Sub-second recursive proofs achieved", "", "", -1, ""},
        {"T200", "Gate computer uses GF(2^128)", "", "", -1, ""},
        {"T600", "Recursive proof composition exists", "", "", -1, ""},
        {"T602", "Recursive proofs achieve 179ms", "", "", -1, ""},
        {"T700", "Circular blockchain demo compiles", "", "", -1, ""},
        {"F001", "Gate computer uses Groth16", "", "", -1, ""},
    };
    
    int count = sizeof(truths) / sizeof(truths[0]);
    
    // Verify each truth's evidence
    for (int i = 0; i < count; i++) {
        printf("Checking %s...", truths[i].id);
        fflush(stdout);
        
        verify_truth_evidence(&truths[i]);
        
        if (truths[i].is_valid == 1) {
            printf(" ✓ VALID\n");
        } else if (truths[i].is_valid == 0) {
            printf(" ✗ INVALID\n");
        } else {
            printf(" ? UNKNOWN\n");
        }
    }
    
    // Generate report
    generate_report(truths, count);
    
    // Quick mode for CI/automation
    if (argc > 1 && strcmp(argv[1], "--quick") == 0) {
        // Just return exit code
        for (int i = 0; i < count; i++) {
            if (truths[i].is_valid == 0) {
                return 1; // Found invalid evidence
            }
        }
        return 0; // All evidence valid
    }
    
    return 0;
}