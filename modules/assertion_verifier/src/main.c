/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "assertion_verifier.h"
#include <stdio.h>
#include <string.h>

int main(void) {
    printf("SHA3 ASSERTION VERIFICATION CHAIN\n");
    printf("Using SHA3 for all node IDs and validity proofs\n");
    printf("C99 + CMake implementation\n\n");
    
    /* Initialize chain */
    assertion_chain_t chain;
    assertion_chain_init(&chain);
    
    /* Define assertions */
    struct {
        const char *statement;
        const char *fopl;
        int deps[MAX_DEPENDENCIES];
        int num_deps;
    } assertions[] = {
        /* Base axioms (no dependencies) */
        {
            "SHA3 is the only allowed hash function",
            "∀h∀op(HashOp(op) ∧ InSystem(op) → SHA3(op))",
            {}, 0
        },
        {
            "Zero-knowledge is mandatory",
            "∀x(Config(x) → EnableZK(x))",
            {}, 0
        },
        /* Derived assertions */
        {
            "All Merkle trees use SHA3",
            "∀m(MerkleTree(m) → UsesSHA3(m))",
            {0}, 1  /* Depends on first assertion */
        },
        {
            "Gate Computer has zero-knowledge enabled",
            "Config(gate_computer) ∧ EnableZK(gate_computer)",
            {1}, 1  /* Depends on second assertion */
        },
        {
            "The system achieves 121-bit security",
            "SecurityLevel(gate_computer) ≥ 121",
            {0, 1}, 2  /* Depends on both axioms */
        },
        {
            "Proofs are post-quantum secure",
            "∀p(Proof(p) → PostQuantumSecure(p))",
            {4}, 1  /* Depends on security level */
        }
    };
    
    /* Add all assertions to chain */
    int indices[10];
    for (int i = 0; i < 6; i++) {
        /* Convert dependency indices to node IDs */
        uint8_t deps[MAX_DEPENDENCIES][NODE_ID_SIZE];
        for (int j = 0; j < assertions[i].num_deps; j++) {
            int dep_idx = assertions[i].deps[j];
            memcpy(deps[j], chain.assertions[dep_idx].node_id, NODE_ID_SIZE);
        }
        
        indices[i] = assertion_chain_add(&chain,
                                       assertions[i].statement,
                                       assertions[i].fopl,
                                       (const uint8_t (*)[NODE_ID_SIZE])deps,
                                       assertions[i].num_deps);
    }
    
    /* Verify the chain */
    verify_assertion_chain(&chain);
    
    /* Print summary */
    print_chain_summary(&chain);
    
    printf("\n✨ Each verified assertion has:\n");
    printf("   1. SHA3-based node ID\n");
    printf("   2. 99%% consensus from both AIs\n");
    printf("   3. Machine-verified FOPL proof\n");
    printf("   4. SHA3 validity certificate\n");
    
    return 0;
}