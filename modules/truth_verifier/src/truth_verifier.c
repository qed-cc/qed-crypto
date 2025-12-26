/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "truth_verifier.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Maximum number of truths we can register */
#define MAX_TRUTHS 1024

/* Internal storage for registered truths */
static truth_statement_t *registered_truths[MAX_TRUTHS];
static size_t truth_count = 0;
static bool initialized = false;

/* Bucket type names for reporting */
static const char *bucket_type_names[] = {
    "TRUTH",
    "FALSE",
    "DERIVED",
    "UNCERTAIN",
    "PHILOSOPHICAL"
};

/* Initialize the truth verification system */
int truth_verifier_init(void) {
    if (initialized) {
        return 0;
    }
    
    memset(registered_truths, 0, sizeof(registered_truths));
    truth_count = 0;
    initialized = true;
    
    return 0;
}

/* Register a truth statement */
int truth_verifier_register(const truth_statement_t *truth) {
    if (!initialized) {
        fprintf(stderr, "Error: truth_verifier not initialized\n");
        return -1;
    }
    
    if (!truth || !truth->id || !truth->statement || !truth->verify) {
        fprintf(stderr, "Error: invalid truth statement\n");
        return -1;
    }
    
    if (truth_count >= MAX_TRUTHS) {
        fprintf(stderr, "Error: maximum truths reached\n");
        return -1;
    }
    
    /* Allocate memory and copy the truth */
    truth_statement_t *copy = malloc(sizeof(truth_statement_t));
    if (!copy) {
        fprintf(stderr, "Error: memory allocation failed\n");
        return -1;
    }
    
    *copy = *truth;
    registered_truths[truth_count++] = copy;
    
    return 0;
}

/* Verify a specific truth by ID */
truth_result_t truth_verifier_verify_by_id(const char *id, char *details, size_t details_size) {
    if (!initialized || !id) {
        return TRUTH_NOT_APPLICABLE;
    }
    
    for (size_t i = 0; i < truth_count; i++) {
        if (strcmp(registered_truths[i]->id, id) == 0) {
            return registered_truths[i]->verify(details, details_size);
        }
    }
    
    if (details && details_size > 0) {
        snprintf(details, details_size, "Truth ID '%s' not found", id);
    }
    return TRUTH_NOT_APPLICABLE;
}

/* Verify all registered truths */
int truth_verifier_verify_all(bool verbose) {
    if (!initialized) {
        fprintf(stderr, "Error: truth_verifier not initialized\n");
        return -1;
    }
    
    int verified = 0;
    int failed = 0;
    int uncertain = 0;
    int not_applicable = 0;
    
    printf("=== TRUTH VERIFICATION REPORT ===\n");
    printf("Total registered truths: %zu\n\n", truth_count);
    
    for (size_t i = 0; i < truth_count; i++) {
        truth_statement_t *truth = registered_truths[i];
        char details[1024] = {0};
        
        truth_result_t result = truth->verify(details, sizeof(details));
        
        const char *status;
        switch (result) {
            case TRUTH_VERIFIED:
                status = "✓ VERIFIED";
                verified++;
                break;
            case TRUTH_FAILED:
                status = "✗ FAILED";
                failed++;
                break;
            case TRUTH_UNCERTAIN:
                status = "? UNCERTAIN";
                uncertain++;
                break;
            case TRUTH_NOT_APPLICABLE:
                status = "- N/A";
                not_applicable++;
                break;
        }
        
        printf("[%s] %s (%s)\n", truth->id, status, bucket_type_names[truth->type]);
        printf("  Statement: %s\n", truth->statement);
        if (verbose && details[0]) {
            printf("  Details: %s\n", details);
        }
        printf("\n");
    }
    
    printf("=== SUMMARY ===\n");
    printf("Verified: %d\n", verified);
    printf("Failed: %d\n", failed);
    printf("Uncertain: %d\n", uncertain);
    printf("Not Applicable: %d\n", not_applicable);
    printf("Total: %zu\n", truth_count);
    
    return (failed == 0) ? 0 : -1;
}

/* Generate a report of all truths */
int truth_verifier_report(const char *output_file, bool include_details) {
    if (!initialized) {
        fprintf(stderr, "Error: truth_verifier not initialized\n");
        return -1;
    }
    
    FILE *fp = output_file ? fopen(output_file, "w") : stdout;
    if (!fp) {
        fprintf(stderr, "Error: cannot open output file\n");
        return -1;
    }
    
    time_t now = time(NULL);
    fprintf(fp, "# Truth Verification Report\n");
    fprintf(fp, "Generated: %s\n", ctime(&now));
    fprintf(fp, "Total truths: %zu\n\n", truth_count);
    
    /* Group by bucket type */
    for (int type = 0; type < 5; type++) {
        fprintf(fp, "## %s Statements\n\n", bucket_type_names[type]);
        
        for (size_t i = 0; i < truth_count; i++) {
            if (registered_truths[i]->type == type) {
                truth_statement_t *truth = registered_truths[i];
                char details[1024] = {0};
                
                truth_result_t result = truth->verify(details, sizeof(details));
                
                fprintf(fp, "### %s: %s\n", truth->id, truth->statement);
                fprintf(fp, "- Category: %s\n", truth->category ? truth->category : "general");
                fprintf(fp, "- Status: %s\n", 
                    result == TRUTH_VERIFIED ? "Verified" :
                    result == TRUTH_FAILED ? "Failed" :
                    result == TRUTH_UNCERTAIN ? "Uncertain" : "Not Applicable");
                
                if (include_details && details[0]) {
                    fprintf(fp, "- Details: %s\n", details);
                }
                fprintf(fp, "\n");
            }
        }
    }
    
    if (fp != stdout) {
        fclose(fp);
    }
    
    return 0;
}

/* Get count of registered truths */
size_t truth_verifier_get_count(void) {
    return truth_count;
}

/* Get count by bucket type */
size_t truth_verifier_get_count_by_type(truth_bucket_type_t type) {
    size_t count = 0;
    for (size_t i = 0; i < truth_count; i++) {
        if (registered_truths[i]->type == type) {
            count++;
        }
    }
    return count;
}

/* Clean up resources */
void truth_verifier_cleanup(void) {
    for (size_t i = 0; i < truth_count; i++) {
        free(registered_truths[i]);
    }
    truth_count = 0;
    initialized = false;
}