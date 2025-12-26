/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "truth_verifier.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <getopt.h>

/* External functions to register truths */
extern void register_cmptr_truths(void);
extern void register_performance_truths(void);
extern void register_security_truths(void);
extern void register_implementation_truths(void);
extern void register_performance_falses(void);
extern void register_future_uncertain(void);
extern void register_optimization_truths(void);
extern void register_optimization_false_buckets(void);
extern void register_soundness_wip_truths(void);
extern void register_proving_time_wip_truths(void);
extern void register_recursive_optimization_truths(void);
extern void register_recursive_advanced_truths(void);
extern void register_zero_knowledge_axiom(void);
extern void register_recursive_final_truths(void);
extern void register_empirical_truths(void);
extern void register_reality_check_truths(void);
extern void register_achievement_truths(void);
extern void register_security_proof_truths(void);
extern void register_sub_second_optimization_truths(void);
extern void register_optimized_security_truths(void);
extern void register_circular_recursion_truths(void);
extern void register_circular_recursion_wip_truths(void);
extern void register_circular_recursion_achieved_truths(void);
extern void register_proof_timing_truths(void);
extern void register_truth_dependency_system(void);
extern void register_circuit_security_axioms(void);
extern void register_confidence_boost_wip_truths(void);
extern void register_recursive_pos_truths(void);
extern void register_detective_findings_truths(void);

static void print_usage(const char *program_name) {
    printf("Usage: %s [OPTIONS]\n", program_name);
    printf("\nOptions:\n");
    printf("  -h, --help           Show this help message\n");
    printf("  -v, --verbose        Show detailed verification results\n");
    printf("  -r, --report FILE    Generate report to FILE (use '-' for stdout)\n");
    printf("  -i, --id ID          Verify specific truth by ID\n");
    printf("  -l, --list           List all registered truths\n");
    printf("  -s, --summary        Show summary statistics only\n");
    printf("\n");
}

static void list_truths(void) {
    printf("=== REGISTERED TRUTHS ===\n\n");
    
    size_t total = truth_verifier_get_count();
    printf("Total: %zu truths\n\n", total);
    
    printf("By Type:\n");
    printf("  TRUTH (T###):         %zu\n", truth_verifier_get_count_by_type(BUCKET_TRUTH));
    printf("  FALSE (F###):         %zu\n", truth_verifier_get_count_by_type(BUCKET_FALSE));
    printf("  DERIVED (D###):       %zu\n", truth_verifier_get_count_by_type(BUCKET_DERIVED));
    printf("  UNCERTAIN (U###):     %zu\n", truth_verifier_get_count_by_type(BUCKET_UNCERTAIN));
    printf("  PHILOSOPHICAL (P###): %zu\n", truth_verifier_get_count_by_type(BUCKET_PHILOSOPHICAL));
}

int main(int argc, char *argv[]) {
    bool verbose = false;
    const char *report_file = NULL;
    const char *verify_id = NULL;
    bool list_mode = false;
    bool summary_only = false;
    
    /* Parse command line options */
    static struct option long_options[] = {
        {"help", no_argument, 0, 'h'},
        {"verbose", no_argument, 0, 'v'},
        {"report", required_argument, 0, 'r'},
        {"id", required_argument, 0, 'i'},
        {"list", no_argument, 0, 'l'},
        {"summary", no_argument, 0, 's'},
        {0, 0, 0, 0}
    };
    
    int opt;
    while ((opt = getopt_long(argc, argv, "hvr:i:ls", long_options, NULL)) != -1) {
        switch (opt) {
            case 'h':
                print_usage(argv[0]);
                return 0;
            case 'v':
                verbose = true;
                break;
            case 'r':
                report_file = optarg;
                break;
            case 'i':
                verify_id = optarg;
                break;
            case 'l':
                list_mode = true;
                break;
            case 's':
                summary_only = true;
                break;
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    
    /* Initialize the truth verifier */
    if (truth_verifier_init() != 0) {
        fprintf(stderr, "Failed to initialize truth verifier\n");
        return 1;
    }
    
    /* Register all cmptr truths */
    register_cmptr_truths();
    
    /* Register new comprehensive truth categories */
    register_performance_truths();
    register_security_truths();
    register_implementation_truths();
    register_performance_falses();
    register_future_uncertain();
    
    /* Register optimization truths with SHA3 constraint */
    register_optimization_truths();
    register_optimization_false_buckets();
    
    /* Register soundness amplification WIP truths */
    register_soundness_wip_truths();
    
    /* Register proving time optimization WIP truths */
    register_proving_time_wip_truths();
    
    /* Register recursive optimization proven truths */
    register_recursive_optimization_truths();
    register_recursive_advanced_truths();
    
    /* Register zero-knowledge axiom and truths */
    register_zero_knowledge_axiom();
    
    /* Register final recursive optimization truths */
    register_recursive_final_truths();
    
    /* Register empirical measurement truths */
    register_empirical_truths();
    
    /* Register reality check truths */
    register_reality_check_truths();
    
    /* Register achievement truths */
    register_achievement_truths();
    
    /* Register security proof truths */
    register_security_proof_truths();
    
    /* Register optimization truths */
    register_sub_second_optimization_truths();
    register_optimized_security_truths();
    
    /* Circular recursion truths */
    register_circular_recursion_truths();
    register_circular_recursion_wip_truths();
    register_circular_recursion_achieved_truths();
    
    /* Proof timing investigation */
    // register_proof_timing_truths();  // Missing implementation
    
    /* Truth dependency system for 99% confidence */
    register_truth_dependency_system();
    
    /* Mathematical axioms and circuit security */
    register_circuit_security_axioms();
    
    /* Confidence boost WIP truths for 99% target */
    register_confidence_boost_wip_truths();
    
    /* Recursive PoS implementation truths */
    register_recursive_pos_truths();
    
    /* PoS optimization truths */
    extern void register_pos_optimization_truths(void);
    register_pos_optimization_truths();
    
    /* Detective findings - correcting misconceptions */
    register_detective_findings_truths();
    
    /* Handle different modes */
    if (list_mode) {
        list_truths();
    } else if (verify_id) {
        /* Verify specific truth */
        char details[1024] = {0};
        truth_result_t result = truth_verifier_verify_by_id(verify_id, details, sizeof(details));
        
        const char *status;
        switch (result) {
            case TRUTH_VERIFIED:
                status = "VERIFIED";
                break;
            case TRUTH_FAILED:
                status = "FAILED";
                break;
            case TRUTH_UNCERTAIN:
                status = "UNCERTAIN";
                break;
            case TRUTH_NOT_APPLICABLE:
                status = "NOT APPLICABLE";
                break;
        }
        
        printf("Truth %s: %s\n", verify_id, status);
        if (details[0]) {
            printf("Details: %s\n", details);
        }
        
        return (result == TRUTH_VERIFIED) ? 0 : 1;
    } else if (report_file) {
        /* Generate report */
        const char *output = strcmp(report_file, "-") == 0 ? NULL : report_file;
        return truth_verifier_report(output, verbose);
    } else if (summary_only) {
        /* Just show summary */
        list_truths();
    } else {
        /* Default: verify all truths */
        int result = truth_verifier_verify_all(verbose);
        truth_verifier_cleanup();
        return result;
    }
    
    truth_verifier_cleanup();
    return 0;
}