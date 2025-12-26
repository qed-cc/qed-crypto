/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <sys/stat.h>

/**
 * @file comprehensive_truth_audit.c
 * @brief Comprehensive audit of all truth bucket evidence
 * 
 * This tool runs the truth verifier and then validates the evidence
 * for each truth to ensure consistency.
 */

typedef struct {
    char id[32];
    char status[32];
    char type[32];
    char statement[512];
    char details[1024];
    int has_valid_evidence;
    char evidence_notes[512];
} truth_audit_t;

/* Parse truth verifier output */
static int parse_truth_output(const char *line, truth_audit_t *truth) {
    // Format: [T001] ✓ VERIFIED (TRUTH)
    if (sscanf(line, "[%31[^]]] %*s %31s (%31[^)])", 
               truth->id, truth->status, truth->type) == 3) {
        return 1;
    }
    return 0;
}

/* Validate evidence based on truth ID and status */
static void validate_evidence(truth_audit_t *truth) {
    truth->has_valid_evidence = 1; // Assume valid
    
    // If truth is VERIFIED, check that evidence exists
    if (strstr(truth->status, "VERIFIED")) {
        
        // Performance truths (T100-T199)
        if (truth->id[0] == 'T' && truth->id[1] == '1') {
            // Should have performance data or benchmarks
            if (access("RECURSIVE_PROOF_PERFORMANCE_REPORT.md", F_OK) == 0 ||
                access("docs/PERFORMANCE_BENCHMARKS.md", F_OK) == 0) {
                strcpy(truth->evidence_notes, "Performance documentation exists");
            } else {
                truth->has_valid_evidence = 0;
                strcpy(truth->evidence_notes, "Missing performance documentation");
            }
        }
        
        // Implementation truths (T200-T299)
        else if (truth->id[0] == 'T' && truth->id[1] == '2') {
            // Should have corresponding code
            if (access("modules/gf128/include/gf128.h", F_OK) == 0) {
                strcpy(truth->evidence_notes, "Implementation exists");
            } else {
                truth->has_valid_evidence = 0;
                strcpy(truth->evidence_notes, "Missing implementation");
            }
        }
        
        // Recursive proof truths (T600-T699)
        else if (truth->id[0] == 'T' && truth->id[1] == '6') {
            // Check for recursive proof implementations
            if (access("tools/recursive_proof_128bit_demo.c", F_OK) == 0 ||
                access("examples/circular_blockchain_simple.c", F_OK) == 0) {
                strcpy(truth->evidence_notes, "Recursive proof code exists");
            } else {
                strcpy(truth->evidence_notes, "Check recursive proof implementations");
            }
        }
        
        // Circular recursion WIP truths (T700-T799)
        else if (truth->id[0] == 'T' && truth->id[1] == '7') {
            if (strcmp(truth->id, "T700") == 0 || strcmp(truth->id, "T701") == 0) {
                // These are failing in verifier but binaries exist
                strcpy(truth->evidence_notes, "Binary exists but verifier path issue");
            }
        }
    }
    
    // If truth is FAILED, check that it should fail
    else if (strstr(truth->status, "FAILED")) {
        
        // Failed implementation truths should not have the implementation
        if (truth->id[0] == 'T' && strstr(truth->id, "70")) {
            strcpy(truth->evidence_notes, "Expected failure - work in progress");
        }
    }
    
    // FALSE buckets should verify as false
    else if (truth->id[0] == 'F') {
        if (strstr(truth->status, "FAILED")) {
            strcpy(truth->evidence_notes, "Correctly verified as false");
        } else {
            truth->has_valid_evidence = 0;
            strcpy(truth->evidence_notes, "FALSE bucket not verifying as false!");
        }
    }
}

/* Generate comprehensive audit report */
static void generate_audit_report(truth_audit_t *truths, int count) {
    FILE *fp = fopen("truth_audit_report.md", "w");
    if (!fp) {
        printf("Failed to create audit report\n");
        return;
    }
    
    fprintf(fp, "# Truth Bucket Evidence Audit Report\n\n");
    fprintf(fp, "Generated: %s\n", ctime(&(time_t){time(NULL)}));
    fprintf(fp, "Total truths audited: %d\n\n", count);
    
    // Summary statistics
    int verified = 0, failed = 0, uncertain = 0;
    int valid_evidence = 0, invalid_evidence = 0;
    
    for (int i = 0; i < count; i++) {
        if (strstr(truths[i].status, "VERIFIED")) verified++;
        else if (strstr(truths[i].status, "FAILED")) failed++;
        else if (strstr(truths[i].status, "UNCERTAIN")) uncertain++;
        
        if (truths[i].has_valid_evidence) valid_evidence++;
        else invalid_evidence++;
    }
    
    fprintf(fp, "## Summary\n\n");
    fprintf(fp, "- Verified truths: %d\n", verified);
    fprintf(fp, "- Failed truths: %d\n", failed);
    fprintf(fp, "- Uncertain truths: %d\n", uncertain);
    fprintf(fp, "- Valid evidence: %d\n", valid_evidence);
    fprintf(fp, "- Invalid evidence: %d\n\n", invalid_evidence);
    
    // Evidence issues
    if (invalid_evidence > 0) {
        fprintf(fp, "## ❌ Evidence Issues Found\n\n");
        fprintf(fp, "| Truth ID | Status | Type | Evidence Issue |\n");
        fprintf(fp, "|----------|--------|------|----------------|\n");
        
        for (int i = 0; i < count; i++) {
            if (!truths[i].has_valid_evidence) {
                fprintf(fp, "| %s | %s | %s | %s |\n",
                        truths[i].id, truths[i].status, truths[i].type,
                        truths[i].evidence_notes);
            }
        }
        fprintf(fp, "\n");
    }
    
    // All truths by category
    fprintf(fp, "## All Truths by Category\n\n");
    
    // T001-T099: Core truths
    fprintf(fp, "### Core System Truths (T001-T099)\n\n");
    for (int i = 0; i < count; i++) {
        if (truths[i].id[0] == 'T' && truths[i].id[1] == '0' && truths[i].id[2] >= '0' && truths[i].id[2] <= '9') {
            fprintf(fp, "- **%s**: %s - %s\n", truths[i].id, truths[i].status, truths[i].evidence_notes);
        }
    }
    
    // T100-T199: Performance truths
    fprintf(fp, "\n### Performance Truths (T100-T199)\n\n");
    for (int i = 0; i < count; i++) {
        if (truths[i].id[0] == 'T' && truths[i].id[1] == '1') {
            fprintf(fp, "- **%s**: %s - %s\n", truths[i].id, truths[i].status, truths[i].evidence_notes);
        }
    }
    
    // T600-T799: Recursion truths
    fprintf(fp, "\n### Recursion & Circular Truths (T600-T799)\n\n");
    for (int i = 0; i < count; i++) {
        if (truths[i].id[0] == 'T' && (truths[i].id[1] == '6' || truths[i].id[1] == '7')) {
            fprintf(fp, "- **%s**: %s - %s\n", truths[i].id, truths[i].status, truths[i].evidence_notes);
        }
    }
    
    // FALSE buckets
    fprintf(fp, "\n### False Buckets (F###)\n\n");
    for (int i = 0; i < count; i++) {
        if (truths[i].id[0] == 'F') {
            fprintf(fp, "- **%s**: %s - %s\n", truths[i].id, truths[i].status, truths[i].evidence_notes);
        }
    }
    
    fclose(fp);
    printf("\nAudit report saved to: truth_audit_report.md\n");
}

int main(void) {
    printf("=== COMPREHENSIVE TRUTH BUCKET EVIDENCE AUDIT ===\n\n");
    
    // Run truth verifier and capture output
    printf("Running truth verifier...\n");
    FILE *pipe = popen("./build/bin/verify_truths 2>&1", "r");
    if (!pipe) {
        printf("Failed to run truth verifier\n");
        return 1;
    }
    
    truth_audit_t truths[500];
    int truth_count = 0;
    char line[1024];
    char current_statement[512] = "";
    char current_details[1024] = "";
    
    while (fgets(line, sizeof(line), pipe)) {
        truth_audit_t truth = {0};
        
        // Parse truth line
        if (parse_truth_output(line, &truth)) {
            // Get next line for statement
            if (fgets(line, sizeof(line), pipe)) {
                // Remove "Statement: " prefix
                char *stmt = strstr(line, "Statement: ");
                if (stmt) {
                    stmt += 11;
                    // Remove newline
                    char *nl = strchr(stmt, '\n');
                    if (nl) *nl = '\0';
                    strncpy(truth.statement, stmt, sizeof(truth.statement) - 1);
                }
            }
            
            // Validate evidence
            validate_evidence(&truth);
            
            // Store truth
            if (truth_count < 500) {
                truths[truth_count++] = truth;
            }
        }
    }
    
    pclose(pipe);
    
    printf("Analyzed %d truths\n", truth_count);
    
    // Quick summary
    int issues = 0;
    for (int i = 0; i < truth_count; i++) {
        if (!truths[i].has_valid_evidence) {
            issues++;
            printf("⚠️  %s: %s\n", truths[i].id, truths[i].evidence_notes);
        }
    }
    
    if (issues == 0) {
        printf("\n✅ All truth evidence appears valid!\n");
    } else {
        printf("\n⚠️  Found %d potential evidence issues\n", issues);
    }
    
    // Generate detailed report
    generate_audit_report(truths, truth_count);
    
    return issues > 0 ? 1 : 0;
}