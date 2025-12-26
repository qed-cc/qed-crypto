/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef ASSERTION_VERIFIER_H
#define ASSERTION_VERIFIER_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/* SHA3 hash sizes */
#define SHA3_256_SIZE 32
#define NODE_ID_SIZE 16  /* First 16 bytes of SHA3 */

/* Maximum sizes */
#define MAX_STATEMENT_LEN 512
#define MAX_FORMULA_LEN 512
#define MAX_DEPENDENCIES 10
#define MAX_PROOF_STEPS 20
#define MAX_ASSERTIONS 1000

/* Confidence threshold */
#define CONSENSUS_THRESHOLD 99.0

/* FOPL proof rules */
typedef enum {
    RULE_AXIOM,
    RULE_PREMISE,
    RULE_MODUS_PONENS,
    RULE_UNIVERSAL_INSTANTIATION,
    RULE_EXISTENTIAL_GENERALIZATION,
    RULE_CONJUNCTION,
    RULE_DEFINITION,
    RULE_ARITHMETIC
} fopl_rule_t;

/* Verification status */
typedef enum {
    STATUS_PENDING,
    STATUS_VERIFIED,
    STATUS_FAILED_CONSENSUS,
    STATUS_FAILED_FOPL,
    STATUS_FAILED_DEPENDENCY
} verification_status_t;

/* FOPL formula */
typedef struct {
    char formula[MAX_FORMULA_LEN];
    uint8_t sha3_id[NODE_ID_SIZE];
} fopl_formula_t;

/* Proof step */
typedef struct {
    fopl_rule_t rule;
    fopl_formula_t formula;
    int justification[2];  /* References to previous steps */
    char english[256];
    uint8_t validity_hash[SHA3_256_SIZE];
} proof_step_t;

/* Assertion */
typedef struct {
    char statement[MAX_STATEMENT_LEN];
    fopl_formula_t fopl;
    uint8_t node_id[NODE_ID_SIZE];
    uint8_t dependencies[MAX_DEPENDENCIES][NODE_ID_SIZE];
    int num_dependencies;
    double claude_confidence;
    double openai_confidence;
    verification_status_t status;
    uint8_t validity_certificate[SHA3_256_SIZE];
} assertion_t;

/* Assertion chain */
typedef struct {
    assertion_t assertions[MAX_ASSERTIONS];
    int num_assertions;
    uint8_t tree_root[SHA3_256_SIZE];
} assertion_chain_t;

/* Core functions */

/* Initialize assertion chain */
void assertion_chain_init(assertion_chain_t *chain);

/* Add assertion to chain */
int assertion_chain_add(assertion_chain_t *chain,
                       const char *statement,
                       const char *fopl_formula,
                       const uint8_t dependencies[][NODE_ID_SIZE],
                       int num_dependencies);

/* Conduct AI consensus debate (simulated) */
bool ai_consensus_debate(assertion_t *assertion);

/* Build FOPL proof */
bool fopl_build_proof(assertion_t *assertion, 
                     proof_step_t steps[MAX_PROOF_STEPS],
                     int *num_steps);

/* Verify FOPL proof */
bool fopl_verify_proof(const proof_step_t steps[], int num_steps);

/* Verify complete assertion */
verification_status_t verify_assertion(assertion_t *assertion,
                                     const assertion_chain_t *chain);

/* Verify entire chain */
void verify_assertion_chain(assertion_chain_t *chain);

/* Generate SHA3 validity certificate */
void generate_validity_certificate(const assertion_t *assertion,
                                 const proof_step_t steps[],
                                 int num_steps,
                                 uint8_t certificate[SHA3_256_SIZE]);

/* Build Merkle tree root */
void build_tree_root(assertion_chain_t *chain);

/* Print chain summary */
void print_chain_summary(const assertion_chain_t *chain);

/* Utility functions */
void sha3_node_id(const char *data, uint8_t node_id[NODE_ID_SIZE]);
void print_hex(const uint8_t *data, size_t len);

#endif /* ASSERTION_VERIFIER_H */