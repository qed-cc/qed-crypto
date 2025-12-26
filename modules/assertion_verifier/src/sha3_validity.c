/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "assertion_verifier.h"
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <sha3.h>

/* Generate SHA3 validity certificate for verified assertion */
void generate_validity_certificate(const assertion_t *assertion,
                                 const proof_step_t steps[],
                                 int num_steps,
                                 uint8_t certificate[SHA3_256_SIZE]) {
    
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    
    /* Hash assertion data */
    sha3_update(&ctx, (const uint8_t *)assertion->statement, 
                strlen(assertion->statement));
    sha3_update(&ctx, (const uint8_t *)assertion->fopl.formula,
                strlen(assertion->fopl.formula));
    sha3_update(&ctx, assertion->node_id, NODE_ID_SIZE);
    
    /* Hash dependencies */
    for (int i = 0; i < assertion->num_dependencies; i++) {
        sha3_update(&ctx, assertion->dependencies[i], NODE_ID_SIZE);
    }
    
    /* Hash confidence levels */
    sha3_update(&ctx, (const uint8_t *)&assertion->claude_confidence,
                sizeof(double));
    sha3_update(&ctx, (const uint8_t *)&assertion->openai_confidence,
                sizeof(double));
    
    /* Hash proof steps */
    for (int i = 0; i < num_steps; i++) {
        sha3_update(&ctx, (const uint8_t *)&steps[i].rule, sizeof(fopl_rule_t));
        sha3_update(&ctx, (const uint8_t *)steps[i].formula.formula,
                    strlen(steps[i].formula.formula));
        
        /* Generate validity hash for this step */
        sha3_ctx step_ctx;
        sha3_init(&step_ctx, SHA3_256);
        sha3_update(&step_ctx, (const uint8_t *)&steps[i].rule, sizeof(fopl_rule_t));
        sha3_update(&step_ctx, (const uint8_t *)steps[i].formula.formula,
                    strlen(steps[i].formula.formula));
        sha3_update(&step_ctx, (const uint8_t *)steps[i].english,
                    strlen(steps[i].english));
        sha3_update(&step_ctx, (const uint8_t *)steps[i].justification,
                    sizeof(steps[i].justification));
        sha3_final(&step_ctx, (uint8_t *)&steps[i].validity_hash, SHA3_256_DIGEST_SIZE);
        
        /* Include step hash in certificate */
        sha3_update(&ctx, steps[i].validity_hash, SHA3_256_SIZE);
    }
    
    /* Add timestamp */
    time_t now = time(NULL);
    sha3_update(&ctx, (const uint8_t *)&now, sizeof(time_t));
    
    /* Generate final certificate */
    sha3_final(&ctx, certificate, SHA3_256_DIGEST_SIZE);
}