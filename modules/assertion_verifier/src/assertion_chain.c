/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "assertion_verifier.h"
#include <stdio.h>
#include <string.h>
#include <sha3.h>

void assertion_chain_init(assertion_chain_t *chain) {
    memset(chain, 0, sizeof(assertion_chain_t));
}

int assertion_chain_add(assertion_chain_t *chain,
                       const char *statement,
                       const char *fopl_formula,
                       const uint8_t dependencies[][NODE_ID_SIZE],
                       int num_dependencies) {
    
    if (chain->num_assertions >= MAX_ASSERTIONS) {
        fprintf(stderr, "❌ Assertion chain full\n");
        return -1;
    }
    
    assertion_t *assertion = &chain->assertions[chain->num_assertions];
    
    /* Set statement and formula */
    strncpy(assertion->statement, statement, MAX_STATEMENT_LEN - 1);
    strncpy(assertion->fopl.formula, fopl_formula, MAX_FORMULA_LEN - 1);
    
    /* Generate SHA3 node ID from statement */
    sha3_node_id(statement, assertion->node_id);
    
    /* Generate SHA3 ID for formula */
    sha3_node_id(fopl_formula, assertion->fopl.sha3_id);
    
    /* Copy dependencies */
    assertion->num_dependencies = num_dependencies;
    for (int i = 0; i < num_dependencies && i < MAX_DEPENDENCIES; i++) {
        memcpy(assertion->dependencies[i], dependencies[i], NODE_ID_SIZE);
    }
    
    /* Initialize status */
    assertion->status = STATUS_PENDING;
    assertion->claude_confidence = 0.0;
    assertion->openai_confidence = 0.0;
    
    printf("📝 Added assertion: ");
    print_hex(assertion->node_id, 8);
    printf("\n   Statement: %s\n", statement);
    printf("   FOPL: %s\n", fopl_formula);
    
    chain->num_assertions++;
    return chain->num_assertions - 1;
}

void verify_assertion_chain(assertion_chain_t *chain) {
    printf("\n🔗 VERIFYING ASSERTION CHAIN\n");
    printf("Each assertion must have:\n");
    printf("  1. SHA3-based node ID\n");
    printf("  2. 99%% confidence from both AIs\n");
    printf("  3. Valid FOPL formula\n");
    printf("  4. All dependencies verified\n");
    for (int i = 0; i < 80; i++) printf("=");
    printf("\n");
    
    /* Verify in order */
    for (int i = 0; i < chain->num_assertions; i++) {
        assertion_t *assertion = &chain->assertions[i];
        
        printf("\nVerifying [%d/%d]: ", i + 1, chain->num_assertions);
        print_hex(assertion->node_id, 8);
        printf("\n");
        
        assertion->status = verify_assertion(assertion, chain);
        
        if (assertion->status == STATUS_VERIFIED) {
            printf("✅ VERIFIED\n");
        } else {
            printf("❌ FAILED (status: %d)\n", assertion->status);
        }
    }
    
    /* Build tree root */
    build_tree_root(chain);
}

verification_status_t verify_assertion(assertion_t *assertion,
                                     const assertion_chain_t *chain) {
    /* Step 1: Check dependencies */
    for (int i = 0; i < assertion->num_dependencies; i++) {
        bool dep_found = false;
        bool dep_verified = false;
        
        /* Find dependency in chain */
        for (int j = 0; j < chain->num_assertions; j++) {
            if (memcmp(chain->assertions[j].node_id, 
                      assertion->dependencies[i], NODE_ID_SIZE) == 0) {
                dep_found = true;
                dep_verified = (chain->assertions[j].status == STATUS_VERIFIED);
                break;
            }
        }
        
        if (!dep_found || !dep_verified) {
            printf("   ❌ Dependency %d not verified\n", i);
            return STATUS_FAILED_DEPENDENCY;
        }
    }
    
    /* Step 2: AI consensus debate */
    if (!ai_consensus_debate(assertion)) {
        return STATUS_FAILED_CONSENSUS;
    }
    
    /* Step 3: Build and verify FOPL proof */
    proof_step_t steps[MAX_PROOF_STEPS];
    int num_steps = 0;
    
    if (!fopl_build_proof(assertion, steps, &num_steps)) {
        return STATUS_FAILED_FOPL;
    }
    
    if (!fopl_verify_proof(steps, num_steps)) {
        return STATUS_FAILED_FOPL;
    }
    
    /* Step 4: Generate validity certificate */
    generate_validity_certificate(assertion, steps, num_steps, 
                                assertion->validity_certificate);
    
    printf("   Certificate: ");
    print_hex(assertion->validity_certificate, 16);
    printf("\n");
    
    return STATUS_VERIFIED;
}

void build_tree_root(assertion_chain_t *chain) {
    /* Concatenate all node IDs and hash */
    uint8_t buffer[MAX_ASSERTIONS * NODE_ID_SIZE];
    int offset = 0;
    
    for (int i = 0; i < chain->num_assertions; i++) {
        memcpy(buffer + offset, chain->assertions[i].node_id, NODE_ID_SIZE);
        offset += NODE_ID_SIZE;
    }
    
    /* Generate tree root */
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, buffer, offset);
    sha3_final(&ctx, chain->tree_root, SHA3_256_DIGEST_SIZE);
}

void print_chain_summary(const assertion_chain_t *chain) {
    printf("\n" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "\n");
    printf("ASSERTION CHAIN SUMMARY\n");
    printf("═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "═" "\n");
    
    int verified = 0, failed_consensus = 0, failed_fopl = 0, failed_deps = 0;
    
    for (int i = 0; i < chain->num_assertions; i++) {
        switch (chain->assertions[i].status) {
            case STATUS_VERIFIED: verified++; break;
            case STATUS_FAILED_CONSENSUS: failed_consensus++; break;
            case STATUS_FAILED_FOPL: failed_fopl++; break;
            case STATUS_FAILED_DEPENDENCY: failed_deps++; break;
            default: break;
        }
    }
    
    printf("Total assertions: %d\n", chain->num_assertions);
    printf("✅ Verified: %d\n", verified);
    printf("❌ Failed consensus: %d\n", failed_consensus);
    printf("❌ Failed FOPL: %d\n", failed_fopl);
    printf("❌ Failed dependencies: %d\n", failed_deps);
    
    printf("\nTree root: ");
    print_hex(chain->tree_root, 16);
    printf("...\n");
    
    if (verified > 0) {
        printf("\n🔗 VERIFIED CHAIN:\n");
        for (int i = 0; i < chain->num_assertions; i++) {
            if (chain->assertions[i].status == STATUS_VERIFIED) {
                printf("%d. ", i + 1);
                print_hex(chain->assertions[i].node_id, 8);
                printf(": %.50s...\n", chain->assertions[i].statement);
            }
        }
    }
}

/* Utilities */
void sha3_node_id(const char *data, uint8_t node_id[NODE_ID_SIZE]) {
    uint8_t hash[SHA3_256_SIZE];
    sha3_ctx ctx;
    
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t *)data, strlen(data));
    sha3_final(&ctx, hash, SHA3_256_DIGEST_SIZE);
    
    memcpy(node_id, hash, NODE_ID_SIZE);
}

void print_hex(const uint8_t *data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        printf("%02x", data[i]);
    }
}