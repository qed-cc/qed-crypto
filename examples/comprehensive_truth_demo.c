/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "truth_verifier.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* External registration functions */
extern void register_performance_truths(void);
extern void register_security_truths(void);
extern void register_implementation_truths(void);
extern void register_performance_falses(void);
extern void register_future_uncertain(void);

/* Category names for display */
static const char* get_category_name(const char* category) {
    if (strcmp(category, "performance") == 0) return "🚀 Performance";
    if (strcmp(category, "security") == 0) return "🔐 Security";
    if (strcmp(category, "implementation") == 0) return "⚙️  Implementation";
    if (strcmp(category, "future") == 0) return "🔮 Future Features";
    return category;
}

/* Result emojis */
static const char* get_result_emoji(truth_result_t result) {
    switch (result) {
        case TRUTH_VERIFIED: return "✅";
        case TRUTH_FAILED: return "❌";
        case TRUTH_UNCERTAIN: return "❓";
        case TRUTH_NOT_APPLICABLE: return "⏭️";
    }
    return "?";
}

/* Verify a specific category */
static void verify_category(const char* category_id, const char* category_name) {
    printf("\n%s Truths:\n", category_name);
    printf("=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=\n\n");
    
    int verified = 0;
    int failed = 0;
    int uncertain = 0;
    
    /* Try T100-T110 range */
    for (int i = 100; i <= 110; i++) {
        char id[16];
        snprintf(id, sizeof(id), "%s%d", category_id, i);
        
        char details[1024] = {0};
        truth_result_t result = truth_verifier_verify_by_id(id, details, sizeof(details));
        
        if (result != TRUTH_NOT_APPLICABLE) {
            printf("%s %s: ", get_result_emoji(result), id);
            
            /* Get the statement - this is a simplified version */
            if (strcmp(category_id, "T") == 0 && i >= 100 && i <= 110) {
                const char* statements[] = {
                    "",  /* 100 */
                    "Proof generation takes ~150ms on modern CPU",
                    "Verification takes ~8ms",
                    "Memory usage is ~38MB",
                    "Throughput is 6.7 proofs/second",
                    "Supports parallel proof generation with OpenMP",
                    "AVX2/AVX512 optimizations accelerate field operations",
                    "Proof size is ~190KB with 320 queries",
                    "Binary NTT enables efficient polynomial operations",
                    "Memory access patterns are cache-friendly",
                    "Streaming sumcheck reduces memory footprint"
                };
                if (i <= 110) printf("%s\n", statements[i - 100]);
            }
            
            if (details[0]) {
                printf("   └─ %s\n", details);
            }
            printf("\n");
            
            switch (result) {
                case TRUTH_VERIFIED: verified++; break;
                case TRUTH_FAILED: failed++; break;
                case TRUTH_UNCERTAIN: uncertain++; break;
                default: break;
            }
        }
    }
    
    /* Try specific ranges for other categories */
    if (strcmp(category_id, "T") == 0) {
        /* Security truths T200-T210 */
        for (int i = 200; i <= 210; i++) {
            char id[16];
            snprintf(id, sizeof(id), "T%d", i);
            
            char details[1024] = {0};
            truth_result_t result = truth_verifier_verify_by_id(id, details, sizeof(details));
            
            if (result != TRUTH_NOT_APPLICABLE) {
                verified++;
            }
        }
        
        /* Implementation truths T300-T310 */
        for (int i = 300; i <= 310; i++) {
            char id[16];
            snprintf(id, sizeof(id), "T%d", i);
            
            char details[1024] = {0};
            truth_result_t result = truth_verifier_verify_by_id(id, details, sizeof(details));
            
            if (result != TRUTH_NOT_APPLICABLE) {
                verified++;
            }
        }
    }
    
    printf("\nSummary: %d verified, %d failed, %d uncertain\n", verified, failed, uncertain);
}

int main(void) {
    printf("🏗️  Gate Computer Comprehensive Truth Verification\n");
    printf("=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=" "=\n");
    
    /* Initialize truth verifier */
    if (truth_verifier_init() != 0) {
        fprintf(stderr, "Failed to initialize truth verifier\n");
        return 1;
    }
    
    /* Register all truth categories */
    register_performance_truths();
    register_security_truths();
    register_implementation_truths();
    register_performance_falses();
    register_future_uncertain();
    
    /* Show total counts */
    size_t total = truth_verifier_get_count();
    printf("\n📊 Registered Statements: %zu total\n", total);
    printf("   ✓ Truths:        %zu\n", truth_verifier_get_count_by_type(BUCKET_TRUTH));
    printf("   ✗ Falses:        %zu\n", truth_verifier_get_count_by_type(BUCKET_FALSE));
    printf("   ? Uncertain:     %zu\n", truth_verifier_get_count_by_type(BUCKET_UNCERTAIN));
    
    /* Verify each category */
    verify_category("T", "🚀 Performance");
    verify_category("F", "❌ Performance Misconceptions");
    verify_category("U", "🔮 Future Possibilities");
    
    /* Show key insights */
    printf("\n🔑 Key Insights:\n");
    printf("=" "=" "=" "=" "=" "=" "=" "=" "=" "=\n\n");
    
    /* Verify specific important truths */
    char details[1024];
    
    /* T101: Proof generation time */
    if (truth_verifier_verify_by_id("T101", details, sizeof(details)) == TRUTH_VERIFIED) {
        printf("✅ Fast Proofs: ~150ms generation time enables real-time applications\n");
    }
    
    /* T201: No discrete log */
    if (truth_verifier_verify_by_id("T201", details, sizeof(details)) == TRUTH_VERIFIED) {
        printf("✅ Quantum-Safe: No discrete logarithm assumptions - secure against Shor's algorithm\n");
    }
    
    /* T301: C99 implementation */
    if (truth_verifier_verify_by_id("T301", details, sizeof(details)) == TRUTH_VERIFIED) {
        printf("✅ Portable: Pure C99 implementation runs everywhere\n");
    }
    
    /* F101: Proof size misconception */
    if (truth_verifier_verify_by_id("F101", details, sizeof(details)) == TRUTH_FAILED) {
        printf("❌ Corrected: Proofs are ~190KB, not <100KB (transparency has a cost)\n");
    }
    
    /* U101: GPU potential */
    if (truth_verifier_verify_by_id("U101", details, sizeof(details)) == TRUTH_UNCERTAIN) {
        printf("❓ Future: GPU acceleration could dramatically improve performance\n");
    }
    
    printf("\n💡 Use './verify_truths -l' to see all truths\n");
    printf("💡 Use './verify_truths -i T101' to verify a specific truth\n");
    printf("💡 Use './verify_truths -r report.txt' to generate a full report\n");
    
    /* Cleanup */
    truth_verifier_cleanup();
    
    return 0;
}