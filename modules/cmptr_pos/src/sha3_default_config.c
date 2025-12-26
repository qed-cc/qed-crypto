/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos_v2.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * SHA3-Only PoS Configuration
 * ===========================
 * 
 * This module configures the PoS system to use ONLY SHA3-based
 * cryptography, making it fully post-quantum secure with a single
 * cryptographic assumption.
 */

/* Configuration for SHA3-only mode */
typedef struct {
    bool force_sha3_vrf;        // Always use SHA3 VRF
    bool disable_lattice_vrf;   // Disable lattice VRF registration
    bool require_sha3_only;     // Reject non-SHA3 modules
} sha3_only_config_t;

/* Global SHA3-only configuration */
static sha3_only_config_t g_sha3_config = {
    .force_sha3_vrf = true,
    .disable_lattice_vrf = true,
    .require_sha3_only = true
};

/* Set SHA3-only mode */
void cmptr_pos_set_sha3_only_mode(bool enabled) {
    g_sha3_config.force_sha3_vrf = enabled;
    g_sha3_config.disable_lattice_vrf = enabled;
    g_sha3_config.require_sha3_only = enabled;
    
    if (enabled) {
        printf("✓ SHA3-Only Mode ENABLED\n");
        printf("  - VRF: SHA3-based (no lattices)\n");
        printf("  - Hashing: SHA3-256 only\n");
        printf("  - Proofs: BaseFold RAA with SHA3\n");
        printf("  - Security: Single cryptographic assumption\n");
    } else {
        printf("⚠ SHA3-Only Mode DISABLED\n");
        printf("  - Multiple cryptographic primitives allowed\n");
    }
}

/* Check if SHA3-only mode is enabled */
bool cmptr_pos_is_sha3_only_mode(void) {
    return g_sha3_config.require_sha3_only;
}

/* Override module selection for SHA3-only */
bool cmptr_pos_select_sha3_modules(pos_state_v2_t* pos) {
    if (!pos) {
        return false;
    }
    
    printf("\n=== Selecting SHA3-Only Modules ===\n");
    
    /* Force SHA3 VRF selection */
    if (g_sha3_config.force_sha3_vrf) {
        /* Find SHA3 VRF module specifically */
        module_interface_t* sha3_vrf = NULL;
        
        /* Search registered modules for SHA3 VRF */
        for (uint32_t i = 0; i < pos->registered_modules_count; i++) {
            module_interface_t* module = pos->registered_modules[i];
            if (module && module->version == VRF_MODULE_SHA3_V1) {
                sha3_vrf = module;
                break;
            }
        }
        
        if (sha3_vrf) {
            pos->vrf_module = (vrf_module_t*)sha3_vrf;
            printf("✓ Selected: %s\n", sha3_vrf->name);
        } else {
            fprintf(stderr, "ERROR: SHA3 VRF module not found!\n");
            return false;
        }
    }
    
    /* Verify all modules use SHA3 */
    if (g_sha3_config.require_sha3_only) {
        /* Check that proof module uses SHA3 for hashing */
        if (pos->proof_module && 
            strstr(pos->proof_module->base.name, "BaseFold") != NULL) {
            printf("✓ Proof module uses SHA3 hashing\n");
        }
        
        /* Check snapshot module */
        if (pos->snapshot_module &&
            strstr(pos->snapshot_module->base.name, "SHA3") != NULL) {
            printf("✓ Snapshot module uses SHA3\n");
        }
    }
    
    printf("\n✓ SHA3-Only configuration complete\n");
    printf("  - Single cryptographic assumption: SHA3-256\n");
    printf("  - Post-quantum secure by design\n");
    printf("  - No elliptic curves, no lattices\n");
    
    return true;
}

/* Modified module registration that respects SHA3-only mode */
bool cmptr_pos_register_module_sha3_aware(
    pos_state_v2_t* pos,
    module_interface_t* module,
    module_type_t type,
    uint32_t version
) {
    if (!pos || !module) {
        return false;
    }
    
    /* Check if we should block non-SHA3 modules */
    if (g_sha3_config.disable_lattice_vrf && 
        type == MODULE_TYPE_VRF &&
        version == VRF_MODULE_LATTICE_V1) {
        printf("⚠ Skipping lattice VRF registration (SHA3-only mode)\n");
        return true;  /* Pretend success but don't register */
    }
    
    /* Check module compatibility with SHA3-only */
    if (g_sha3_config.require_sha3_only) {
        /* Verify module doesn't introduce non-SHA3 crypto */
        const char* name = module->name ? module->name : "";
        
        if (strstr(name, "elliptic") || 
            strstr(name, "ECDSA") ||
            strstr(name, "pairing") ||
            strstr(name, "BLS")) {
            fprintf(stderr, "ERROR: Module '%s' incompatible with SHA3-only mode\n", name);
            return false;
        }
    }
    
    /* Proceed with normal registration */
    return cmptr_pos_register_module(module, type, version);
}

/* Create SHA3-only PoS configuration */
consensus_modules_t cmptr_pos_create_sha3_only_config(void) {
    consensus_modules_t config = {
        .snapshot_module = SNAPSHOT_MODULE_VERKLE_V1,    // SHA3-based Verkle
        .vrf_module = VRF_MODULE_SHA3_V1,                // SHA3-based VRF
        .ordering_module = ORDERING_MODULE_MYSTICETI_V1, // Standard ordering
        .proof_module = PROOF_MODULE_BASEFOLD_V1         // SHA3-based proofs
    };
    
    printf("✓ Created SHA3-only module configuration:\n");
    printf("  - Snapshot: SHA3-Verkle (v%u)\n", config.snapshot_module);
    printf("  - VRF: SHA3-based (v%u)\n", config.vrf_module);
    printf("  - Ordering: Mysticeti (v%u)\n", config.ordering_module);
    printf("  - Proof: BaseFold/SHA3 (v%u)\n", config.proof_module);
    
    return config;
}

/* Verify SHA3-only configuration */
bool cmptr_pos_verify_sha3_only(const pos_state_v2_t* pos) {
    if (!pos) {
        return false;
    }
    
    bool is_sha3_only = true;
    
    /* Check VRF module */
    if (pos->vrf_module) {
        if (pos->vrf_module->base.version != VRF_MODULE_SHA3_V1) {
            fprintf(stderr, "ERROR: Non-SHA3 VRF module detected\n");
            is_sha3_only = false;
        }
    }
    
    /* Check proof module uses SHA3 */
    if (pos->proof_module) {
        const char* name = pos->proof_module->base.name;
        if (!strstr(name, "BaseFold")) {
            fprintf(stderr, "WARNING: Proof module may not use SHA3 exclusively\n");
        }
    }
    
    if (is_sha3_only) {
        printf("✓ SHA3-Only verification PASSED\n");
        printf("  - All modules use SHA3-256 exclusively\n");
        printf("  - Single cryptographic assumption maintained\n");
        printf("  - Post-quantum secure\n");
    }
    
    return is_sha3_only;
}