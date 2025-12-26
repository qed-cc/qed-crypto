/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>

typedef struct {
    char id[16];
    char description[256];
    int is_mathematical;  // Can be formally proven
    int has_fstar_proof;
    int has_coq_proof;
    int has_lean_proof;
    char proof_files[5][256];
    int proof_count;
    int complexity;  // 1-10 scale
} truth_analysis_t;

// Analyze truth bucket implementations
void analyze_truth_file(const char *filepath, truth_analysis_t *truths, int *count) {
    FILE *f = fopen(filepath, "r");
    if (!f) return;
    
    char line[1024];
    char current_truth[16] = {0};
    int in_function = 0;
    
    while (fgets(line, sizeof(line), f)) {
        // Look for verify_T### or verify_F### functions
        if (strstr(line, "verify_T") || strstr(line, "verify_F")) {
            char *start = strstr(line, "verify_");
            if (start) {
                sscanf(start, "verify_%15s", current_truth);
                // Remove trailing characters
                for (int i = 0; i < 16; i++) {
                    if (current_truth[i] == '_' || current_truth[i] == '(') {
                        current_truth[i] = '\0';
                        break;
                    }
                }
                in_function = 1;
                
                // New truth found
                strcpy(truths[*count].id, current_truth);
                truths[*count].is_mathematical = 0;  // Default
                (*count)++;
            }
        }
        
        // Analyze function content for mathematical nature
        if (in_function) {
            // Mathematical indicators
            if (strstr(line, "mathematical") || 
                strstr(line, "theorem") ||
                strstr(line, "proof") ||
                strstr(line, "axiom") ||
                strstr(line, "soundness") ||
                strstr(line, "GF(2^128)") ||
                strstr(line, "polynomial") ||
                strstr(line, "field")) {
                truths[*count - 1].is_mathematical = 1;
            }
            
            // Empirical indicators (cannot be proven)
            if (strstr(line, "benchmark") ||
                strstr(line, "measure") ||
                strstr(line, "elapsed") ||
                strstr(line, "performance") ||
                strstr(line, "file exists") ||
                strstr(line, "runtime")) {
                truths[*count - 1].is_mathematical = 0;
            }
            
            if (strstr(line, "}") && !strstr(line, "{")) {
                in_function = 0;
            }
        }
    }
    
    fclose(f);
}

// Check for existing formal proofs
void check_formal_proofs(truth_analysis_t *truths, int count) {
    // Check F* proofs
    DIR *dir = opendir("modules/truth_verifier/fstar");
    if (dir) {
        struct dirent *entry;
        while ((entry = readdir(dir)) != NULL) {
            if (strstr(entry->d_name, ".fst")) {
                // Check each truth
                for (int i = 0; i < count; i++) {
                    if (truths[i].id[0] && strstr(entry->d_name, truths[i].id)) {
                        truths[i].has_fstar_proof = 1;
                        if (truths[i].proof_count < 5) {
                            strcpy(truths[i].proof_files[truths[i].proof_count++], 
                                   entry->d_name);
                        }
                    }
                }
            }
        }
        closedir(dir);
    }
    
    // Check other proof systems
    const char *proof_dirs[] = {
        "tools/formal_specs",
        "formal_proofs",
        "formal-proofs"
    };
    
    for (int d = 0; d < 3; d++) {
        dir = opendir(proof_dirs[d]);
        if (dir) {
            struct dirent *entry;
            while ((entry = readdir(dir)) != NULL) {
                for (int i = 0; i < count; i++) {
                    if (strstr(entry->d_name, truths[i].id)) {
                        if (strstr(entry->d_name, ".v"))
                            truths[i].has_coq_proof = 1;
                        if (strstr(entry->d_name, ".lean"))
                            truths[i].has_lean_proof = 1;
                    }
                }
            }
            closedir(dir);
        }
    }
}

// Generate comprehensive report
void generate_comprehensive_report(truth_analysis_t *truths, int count) {
    FILE *f = fopen("PROOF_COVERAGE_REPORT.md", "w");
    if (!f) return;
    
    fprintf(f, "# Comprehensive Proof Coverage Report\n\n");
    fprintf(f, "Generated: %s\n\n", __DATE__);
    
    // Statistics
    int mathematical = 0, proven = 0, provable = 0;
    for (int i = 0; i < count; i++) {
        if (truths[i].is_mathematical) {
            mathematical++;
            if (truths[i].has_fstar_proof || 
                truths[i].has_coq_proof || 
                truths[i].has_lean_proof) {
                proven++;
            } else {
                provable++;
            }
        }
    }
    
    fprintf(f, "## Summary Statistics\n\n");
    fprintf(f, "- **Total Truth Buckets**: %d\n", count);
    fprintf(f, "- **Mathematical Truths**: %d (%.1f%%)\n", 
            mathematical, (float)mathematical/count * 100);
    fprintf(f, "- **Already Proven**: %d (%.1f%% of mathematical)\n", 
            proven, mathematical > 0 ? (float)proven/mathematical * 100 : 0);
    fprintf(f, "- **Awaiting Proofs**: %d\n", provable);
    fprintf(f, "- **Empirical Only**: %d\n", count - mathematical);
    
    // Proof opportunities
    fprintf(f, "\n## High-Priority Proof Opportunities\n\n");
    fprintf(f, "| Truth ID | Type | Description | Complexity | Priority |\n");
    fprintf(f, "|----------|------|-------------|------------|----------|\n");
    
    for (int i = 0; i < count; i++) {
        if (truths[i].is_mathematical && !truths[i].has_fstar_proof) {
            const char *priority = "Medium";
            if (strstr(truths[i].id, "A0")) priority = "CRITICAL";  // Axioms
            else if (strstr(truths[i].id, "T00")) priority = "High";  // Core
            else if (strstr(truths[i].id, "T1") || 
                     strstr(truths[i].id, "T2")) priority = "High";
            
            fprintf(f, "| %s | Mathematical | TBD | TBD | %s |\n",
                    truths[i].id, priority);
        }
    }
    
    // Existing proofs
    fprintf(f, "\n## Existing Formal Proofs\n\n");
    fprintf(f, "| Truth ID | F* | Coq | Lean | Files |\n");
    fprintf(f, "|----------|-------|-------|--------|-------|\n");
    
    for (int i = 0; i < count; i++) {
        if (truths[i].has_fstar_proof || 
            truths[i].has_coq_proof || 
            truths[i].has_lean_proof) {
            fprintf(f, "| %s | %s | %s | %s | ",
                    truths[i].id,
                    truths[i].has_fstar_proof ? "✓" : "-",
                    truths[i].has_coq_proof ? "✓" : "-",
                    truths[i].has_lean_proof ? "✓" : "-");
            
            for (int j = 0; j < truths[i].proof_count; j++) {
                fprintf(f, "%s ", truths[i].proof_files[j]);
            }
            fprintf(f, "|\n");
        }
    }
    
    // Implementation plan
    fprintf(f, "\n## Proof Implementation Plan\n\n");
    fprintf(f, "### Phase 1: Core Axioms (Week 1)\n");
    fprintf(f, "- Formalize A001 (SHA3-only) in F*\n");
    fprintf(f, "- Formalize A002 (Zero-knowledge) in F*\n");
    fprintf(f, "- Create type-level enforcement\n\n");
    
    fprintf(f, "### Phase 2: Field Theory (Week 2-3)\n");
    fprintf(f, "- GF(2^128) field axioms\n");
    fprintf(f, "- Polynomial operations\n");
    fprintf(f, "- Multilinear extensions\n\n");
    
    fprintf(f, "### Phase 3: Protocol Proofs (Week 4-6)\n");
    fprintf(f, "- Sumcheck soundness\n");
    fprintf(f, "- FRI proximity testing\n");
    fprintf(f, "- Merkle tree binding\n\n");
    
    fprintf(f, "### Phase 4: Optimizations (Week 7-8)\n");
    fprintf(f, "- SIMD correctness\n");
    fprintf(f, "- Parallel algorithm equivalence\n");
    fprintf(f, "- Cache-oblivious correctness\n\n");
    
    fprintf(f, "### Phase 5: Composition (Week 9-10)\n");
    fprintf(f, "- Recursive proof soundness\n");
    fprintf(f, "- End-to-end security\n");
    fprintf(f, "- Extraction to verified C\n\n");
    
    fclose(f);
    
    printf("Generated comprehensive report: PROOF_COVERAGE_REPORT.md\n");
}

int main() {
    printf("=== Gate Computer Proof Coverage Analyzer ===\n\n");
    
    // Analyze all truth files
    truth_analysis_t truths[1000] = {0};
    int truth_count = 0;
    
    DIR *dir = opendir("modules/truth_verifier/src");
    if (dir) {
        struct dirent *entry;
        while ((entry = readdir(dir)) != NULL) {
            if (strstr(entry->d_name, "_truths.c") || 
                strstr(entry->d_name, "_axioms.c")) {
                char filepath[512];
                snprintf(filepath, sizeof(filepath), 
                         "modules/truth_verifier/src/%s", entry->d_name);
                
                printf("Analyzing: %s\n", entry->d_name);
                analyze_truth_file(filepath, truths, &truth_count);
            }
        }
        closedir(dir);
    }
    
    printf("\nFound %d truth buckets\n", truth_count);
    
    // Check for existing proofs
    check_formal_proofs(truths, truth_count);
    
    // Generate report
    generate_comprehensive_report(truths, truth_count);
    
    // Summary
    int mathematical = 0, proven = 0;
    for (int i = 0; i < truth_count; i++) {
        if (truths[i].is_mathematical) {
            mathematical++;
            if (truths[i].has_fstar_proof) proven++;
        }
    }
    
    printf("\nSummary:\n");
    printf("- Total truths: %d\n", truth_count);
    printf("- Mathematical (provable): %d\n", mathematical);
    printf("- Already proven: %d\n", proven);
    printf("- Need proofs: %d\n", mathematical - proven);
    printf("- Empirical only: %d\n", truth_count - mathematical);
    
    return 0;
}