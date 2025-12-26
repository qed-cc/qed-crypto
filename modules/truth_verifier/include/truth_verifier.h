/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef TRUTH_VERIFIER_H
#define TRUTH_VERIFIER_H

#include <stddef.h>
#include <stdbool.h>

/* Truth bucket types */
typedef enum {
    BUCKET_TRUTH,         /* T### - Verified facts */
    BUCKET_FALSE,         /* F### - Common misconceptions */
    BUCKET_DERIVED,       /* D### - Logical deductions */
    BUCKET_UNCERTAIN,     /* U### - Questions for investigation */
    BUCKET_PHILOSOPHICAL  /* P### - Domain-level principles */
} truth_bucket_type_t;

/* Truth verification result */
typedef enum {
    TRUTH_VERIFIED,       /* Truth successfully verified */
    TRUTH_FAILED,         /* Truth verification failed */
    TRUTH_UNCERTAIN,      /* Cannot determine truth value */
    TRUTH_NOT_APPLICABLE  /* Truth not applicable in this context */
} truth_result_t;

/* Truth statement structure */
typedef struct {
    const char *id;              /* Truth ID (e.g., "T001") */
    truth_bucket_type_t type;    /* Bucket type */
    const char *statement;       /* Truth statement */
    const char *category;        /* Category (e.g., "math", "security") */
    truth_result_t (*verify)(char *details, size_t details_size); /* Verification function */
} truth_statement_t;

/* Initialize the truth verification system */
int truth_verifier_init(void);

/* Register a truth statement */
int truth_verifier_register(const truth_statement_t *truth);

/* Verify a specific truth by ID */
truth_result_t truth_verifier_verify_by_id(const char *id, char *details, size_t details_size);

/* Verify all registered truths */
int truth_verifier_verify_all(bool verbose);

/* Generate a report of all truths */
int truth_verifier_report(const char *output_file, bool include_details);

/* Get count of registered truths */
size_t truth_verifier_get_count(void);

/* Get count by bucket type */
size_t truth_verifier_get_count_by_type(truth_bucket_type_t type);

/* Clean up resources */
void truth_verifier_cleanup(void);

#endif /* TRUTH_VERIFIER_H */