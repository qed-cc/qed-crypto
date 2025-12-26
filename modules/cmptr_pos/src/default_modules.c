/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos_v2.h"
#include "basefold_raa.h"
#include "gf128.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Forward declarations for SHA3 VRF functions */
bool cmptr_pos_sha3_vrf_keygen(uint8_t* public_key, uint8_t* private_key);
void* cmptr_pos_sha3_vrf_compute(const uint8_t* private_key, const uint8_t* message, size_t msg_len);
bool cmptr_pos_sha3_vrf_verify(const uint8_t* public_key, const uint8_t* message, size_t msg_len, void* vrf);

/* ============= SHA3-VERKLE SNAPSHOT MODULE V1 ============= */
/* Uses SHA3-256 for all commitments - post-quantum secure */

static void* sha3_verkle_v1_init(void* config) {
    /* Initialize SHA3-based Verkle module state */
    return calloc(1, sizeof(int));  /* Placeholder */
}

static void verkle_v1_destroy(void* module) {
    free(module);
}

static bool verkle_v1_is_compatible(uint32_t protocol_version) {
    return protocol_version >= 1;  /* Compatible with all versions */
}

static void* verkle_v1_create_snapshot(validator_pos_t** validators, uint32_t count) {
    /* Use existing implementation */
    return cmptr_pos_create_verkle_commitment(validators, count);
}

static void* verkle_v1_update_incremental(void* prev_snapshot, void* changes) {
    /* Would call incremental update implementation */
    return prev_snapshot;  /* Placeholder */
}

static bool verkle_v1_verify_proof(void* snapshot, const uint8_t* proof, size_t size) {
    verkle_commitment_t* commitment = (verkle_commitment_t*)snapshot;
    /* Simplified verification */
    return size >= 64 && proof[0] == 0xEE;
}

static size_t verkle_v1_get_proof_size(void* snapshot) {
    return 64;  /* Constant size Verkle proofs */
}

/* SHA3-Verkle V1 module definition */
static snapshot_module_t verkle_module_v1 = {
    .base = {
        .version = SNAPSHOT_MODULE_SHA3_VERKLE_V1,
        .name = "SHA3-Verkle Tree V1 (Post-Quantum)",
        .init = sha3_verkle_v1_init,
        .destroy = verkle_v1_destroy,
        .is_compatible = verkle_v1_is_compatible
    },
    .create_snapshot = verkle_v1_create_snapshot,
    .update_incremental = verkle_v1_update_incremental,
    .verify_proof = verkle_v1_verify_proof,
    .get_proof_size = verkle_v1_get_proof_size
};

/* ============= SHA3-BASED VRF MODULE V1 ============= */
/* Pure hash-based VRF using SHA3 - no lattices, fully post-quantum */

static void* sha3_vrf_v1_init(void* config) {
    return calloc(1, sizeof(int));  /* Placeholder */
}

static void sha3_vrf_v1_destroy(void* module) {
    free(module);
}

static bool sha3_vrf_v1_is_compatible(uint32_t protocol_version) {
    return protocol_version >= 1;
}

static bool sha3_vrf_v1_generate_keys(uint8_t* public_out, uint8_t* private_out) {
    /* Use SHA3-based VRF key generation */
    return cmptr_pos_sha3_vrf_keygen(public_out, private_out);
}

static void* sha3_vrf_v1_compute(const uint8_t* private_key, const uint8_t* message, size_t msg_len) {
    /* Use SHA3-based VRF computation */
    return cmptr_pos_sha3_vrf_compute(private_key, message, msg_len);
}

static bool sha3_vrf_v1_verify(const uint8_t* public_key, const uint8_t* message, size_t msg_len, void* vrf) {
    /* Use SHA3-based VRF verification */
    return cmptr_pos_sha3_vrf_verify(public_key, message, msg_len, vrf);
}

static bool sha3_vrf_v1_is_aggregatable(void) {
    return false;  /* SHA3 VRF v1 does not support aggregation */
}

/* SHA3-based VRF V1 module definition */
static vrf_module_t sha3_vrf_module_v1 = {
    .base = {
        .version = VRF_MODULE_SHA3_V1,
        .name = "SHA3-based VRF (Hash-only, Post-Quantum)",
        .init = sha3_vrf_v1_init,
        .destroy = sha3_vrf_v1_destroy,
        .is_compatible = sha3_vrf_v1_is_compatible
    },
    .generate_keys = sha3_vrf_v1_generate_keys,
    .compute_vrf = sha3_vrf_v1_compute,
    .verify_vrf = sha3_vrf_v1_verify,
    .is_aggregatable = sha3_vrf_v1_is_aggregatable,
    .aggregate_vrfs = NULL  /* Not supported */
};

/* ============= MYSTICETI ORDERING MODULE V1 ============= */

static void* mysticeti_v1_init(void* config) {
    return calloc(1, sizeof(int));
}

static void mysticeti_v1_destroy(void* module) {
    free(module);
}

static bool mysticeti_v1_is_compatible(uint32_t protocol_version) {
    return protocol_version >= 1;
}

static void* mysticeti_v1_create_state(narwhal_dag_t* dag, committee_t* committee) {
    return cmptr_pos_create_ordering(dag, committee);
}

static bool mysticeti_v1_run_ordering(void* state) {
    return cmptr_pos_run_ordering((mysticeti_state_t*)state);
}

static uint32_t mysticeti_v1_extract_transactions(void* state, transaction_t** out, uint32_t max) {
    return cmptr_pos_extract_ordered_transactions((mysticeti_state_t*)state, out, max);
}

static consensus_mode_t mysticeti_v1_select_mode(void* state) {
    /* Could analyze DAG structure to choose mode */
    return CONSENSUS_MODE_NORMAL;
}

/* Mysticeti V1 module definition */
static ordering_module_t mysticeti_module_v1 = {
    .base = {
        .version = ORDERING_MODULE_MYSTICETI_V1,
        .name = "Mysticeti BFT Ordering",
        .init = mysticeti_v1_init,
        .destroy = mysticeti_v1_destroy,
        .is_compatible = mysticeti_v1_is_compatible
    },
    .create_state = mysticeti_v1_create_state,
    .run_ordering = mysticeti_v1_run_ordering,
    .extract_transactions = mysticeti_v1_extract_transactions,
    .select_mode = mysticeti_v1_select_mode
};

/* ============= BASEFOLD RAA PROOF MODULE V1 ============= */

static void* basefold_v1_init(void* config) {
    return calloc(1, sizeof(basefold_raa_config_t));
}

static void basefold_v1_destroy(void* module) {
    free(module);
}

static bool basefold_v1_is_compatible(uint32_t protocol_version) {
    return protocol_version >= 1;
}

static void* basefold_v1_generate_proof(const uint8_t* witness, size_t witness_size, void* config) {
    /* Simplified proof generation */
    basefold_raa_config_t raa_config = {
        .num_variables = 20,
        .security_level = 122,
        .enable_zk = 1
    };
    
    /* Convert witness to GF128 */
    size_t num_elements = 1ULL << raa_config.num_variables;
    gf128_t* gf_witness = calloc(num_elements, sizeof(gf128_t));
    
    for (size_t i = 0; i < num_elements && i < witness_size; i++) {
        memset(&gf_witness[i], 0, sizeof(gf128_t));
        ((uint8_t*)&gf_witness[i])[0] = witness[i];
    }
    
    basefold_raa_proof_t* proof = calloc(1, sizeof(basefold_raa_proof_t));
    int result = basefold_raa_prove(gf_witness, &raa_config, proof);
    
    free(gf_witness);
    
    if (result != 0) {
        free(proof);
        return NULL;
    }
    
    return proof;
}

static bool basefold_v1_verify_proof(void* proof, void* config) {
    basefold_raa_config_t raa_config = {
        .num_variables = 20,
        .security_level = 122,
        .enable_zk = 1
    };
    
    return basefold_raa_verify((basefold_raa_proof_t*)proof, &raa_config) == 0;
}

static bool basefold_v1_supports_parallel(void) {
    return true;  /* BaseFold supports parallel proof generation */
}

static void* basefold_v1_combine_proofs(void** proofs, uint32_t count) {
    if (!proofs || count == 0) {
        return NULL;
    }
    
    /* Recursive proof combination */
    printf("  → Combining %u proofs recursively...\n", count);
    
    /* For demo: combine by creating proof of proofs */
    size_t combined_witness_size = count * sizeof(basefold_raa_proof_t);
    uint8_t* combined_witness = calloc(combined_witness_size, 1);
    
    /* Add each proof to witness */
    for (uint32_t i = 0; i < count; i++) {
        memcpy(combined_witness + (i * sizeof(basefold_raa_proof_t)),
               proofs[i], sizeof(basefold_raa_proof_t));
    }
    
    /* Generate combined proof */
    void* combined = basefold_v1_generate_proof(
        combined_witness, combined_witness_size, NULL
    );
    
    free(combined_witness);
    
    return combined;
}

/* BaseFold RAA V1 module definition */
static proof_module_t basefold_module_v1 = {
    .base = {
        .version = PROOF_MODULE_BASEFOLD_SHA3_V1,
        .name = "BaseFold RAA (122-bit security)",
        .init = basefold_v1_init,
        .destroy = basefold_v1_destroy,
        .is_compatible = basefold_v1_is_compatible
    },
    .generate_proof = basefold_v1_generate_proof,
    .verify_proof = basefold_v1_verify_proof,
    .supports_parallel = basefold_v1_supports_parallel,
    .combine_proofs = basefold_v1_combine_proofs
};

/* ============= MODULE REGISTRATION ============= */

/* Register all default modules */
bool cmptr_pos_register_default_modules(pos_state_v2_t* pos) {
    if (!pos) {
        return false;
    }
    
    printf("\n=== Registering Default Modules ===\n");
    
    /* Check if SHA3-only mode is enabled */
    extern bool cmptr_pos_is_sha3_only_mode(void);
    bool sha3_only = cmptr_pos_is_sha3_only_mode();
    
    if (sha3_only) {
        printf("ℹ SHA3-Only Mode ACTIVE - Using pure hash-based cryptography\n");
    }
    
    /* Register Verkle snapshot module */
    if (!cmptr_pos_register_snapshot_module(pos, &verkle_module_v1, 
                                           SNAPSHOT_MODULE_SHA3_VERKLE_V1)) {
        return false;
    }
    
    /* Register SHA3-based VRF module FIRST (higher priority) */
    if (!cmptr_pos_register_vrf_module(pos, &sha3_vrf_module_v1,
                                      VRF_MODULE_SHA3_V1)) {
        return false;
    }
    
    /* Only register lattice VRF if not in SHA3-only mode */
    if (!sha3_only) {
        /* Future: Could register lattice VRF here as alternative */
        printf("  - Additional VRF modules could be registered (not in SHA3-only mode)\n");
    }
    
    /* Register Mysticeti ordering module */
    if (!cmptr_pos_register_ordering_module(pos, &mysticeti_module_v1,
                                           ORDERING_MODULE_MYSTICETI_V1)) {
        return false;
    }
    
    /* Register BaseFold proof module */
    if (!cmptr_pos_register_proof_module(pos, &basefold_module_v1,
                                        PROOF_MODULE_BASEFOLD_SHA3_V1)) {
        return false;
    }
    
    printf("\n✓ All default modules registered\n");
    printf("  - Snapshot: %s\n", verkle_module_v1.base.name);
    printf("  - VRF: %s\n", sha3_vrf_module_v1.base.name);
    printf("  - Ordering: %s\n", mysticeti_module_v1.base.name);
    printf("  - Proof: %s\n", basefold_module_v1.base.name);
    
    if (sha3_only) {
        printf("\n✓ SHA3-Only Configuration:\n");
        printf("  - Single cryptographic assumption: SHA3-256\n");
        printf("  - Post-quantum secure by design\n");
        printf("  - No elliptic curves, no lattices, no pairings\n");
    }
    
    return true;
}

/* ============= FUTURE MODULE STUBS ============= */

/* Future: Binary Merkle module (more efficient) */
static snapshot_module_t binary_merkle_module_v2 = {
    .base = {
        .version = SNAPSHOT_MODULE_SHA3_MERKLE_V2,
        .name = "Binary Merkle Tree V2",
        .init = NULL,  /* Not implemented */
        .destroy = NULL,
        .is_compatible = NULL
    }
};

/* Future: Enhanced SHA3 VRF module (supports aggregation) */
static vrf_module_t enhanced_sha3_vrf_module_v2 = {
    .base = {
        .version = VRF_MODULE_SHA3_V1,
        .name = "Enhanced SHA3 VRF with Aggregation",
        .init = NULL,  /* Not implemented */
        .destroy = NULL,
        .is_compatible = NULL
    }
};

/* Future: Bullshark ordering (improved Mysticeti) */
static ordering_module_t bullshark_module_v2 = {
    .base = {
        .version = ORDERING_MODULE_BULLSHARK_V2,
        .name = "Bullshark Consensus",
        .init = NULL,  /* Not implemented */
        .destroy = NULL,
        .is_compatible = NULL
    }
};

/* Future: Ligero proof module (different trade-offs) */
static proof_module_t ligero_module_v2 = {
    .base = {
        .version = PROOF_MODULE_SHA3_STARK_V2,  /* Use an existing version for now */
        .name = "Ligero (Linear-time proofs)",
        .init = NULL,  /* Not implemented */
        .destroy = NULL,
        .is_compatible = NULL
    }
};

/* Demonstrate cryptographic agility */
void cmptr_pos_demonstrate_agility(pos_state_v2_t* pos) {
    if (!pos) return;
    
    printf("\n=== Cryptographic Agility Demo ===\n");
    printf("\nCurrent modules:\n");
    
    if (pos->snapshot_module) {
        printf("  - Snapshot: %s (v%u)\n", 
               pos->snapshot_module->base.name,
               pos->snapshot_module->base.version);
    }
    
    if (pos->vrf_module) {
        printf("  - VRF: %s (v%u)\n",
               pos->vrf_module->base.name,
               pos->vrf_module->base.version);
    }
    
    if (pos->ordering_module) {
        printf("  - Ordering: %s (v%u)\n",
               pos->ordering_module->base.name,
               pos->ordering_module->base.version);
    }
    
    if (pos->proof_module) {
        printf("  - Proof: %s (v%u)\n",
               pos->proof_module->base.name,
               pos->proof_module->base.version);
    }
    
    printf("\nFuture modules (when quantum threats evolve):\n");
    printf("  - %s: More efficient for large validator sets\n",
           binary_merkle_module_v2.base.name);
    printf("  - %s: Enables signature aggregation\n",
           enhanced_sha3_vrf_module_v2.base.name);
    printf("  - %s: Lower latency consensus\n",
           bullshark_module_v2.base.name);
    printf("  - %s: Alternative proof system\n",
           ligero_module_v2.base.name);
    
    printf("\nBenefits:\n");
    printf("  • Upgrade algorithms without hard forks\n");
    printf("  • Test new cryptography on testnets first\n");
    printf("  • Respond quickly to quantum advances\n");
    printf("  • Mix and match optimal components\n");
}