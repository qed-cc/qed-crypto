/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_SHA3_CONFIG_H
#define CMPTR_POS_SHA3_CONFIG_H

#include "cmptr_pos_v2.h"
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * SHA3-Only PoS Configuration
 * ===========================
 * 
 * Functions to configure the PoS system to use ONLY SHA3-based
 * cryptography, achieving post-quantum security with a single
 * cryptographic assumption.
 */

/**
 * Enable or disable SHA3-only mode
 * 
 * When enabled:
 * - Forces SHA3 VRF selection (no lattice VRF)
 * - Uses SHA3-256 for all hashing
 * - Rejects modules that introduce non-SHA3 crypto
 * 
 * @param enabled True to enable SHA3-only mode
 */
void cmptr_pos_set_sha3_only_mode(bool enabled);

/**
 * Check if SHA3-only mode is enabled
 * 
 * @return True if SHA3-only mode is active
 */
bool cmptr_pos_is_sha3_only_mode(void);

/**
 * Select SHA3-only modules for PoS
 * 
 * Forces selection of:
 * - SHA3-based VRF (no lattices)
 * - SHA3-based Verkle trees
 * - BaseFold RAA with SHA3
 * 
 * @param pos PoS state to configure
 * @return True on success
 */
bool cmptr_pos_select_sha3_modules(pos_state_v2_t* pos);

/**
 * Register module with SHA3-only awareness
 * 
 * Blocks registration of modules that would introduce
 * non-SHA3 cryptographic assumptions.
 * 
 * @param pos PoS state
 * @param module Module to register
 * @param type Module type
 * @param version Module version
 * @return True on success
 */
bool cmptr_pos_register_module_sha3_aware(
    pos_state_v2_t* pos,
    module_interface_t* module,
    module_type_t type,
    uint32_t version
);

/**
 * Create SHA3-only module configuration
 * 
 * @return Module configuration for SHA3-only mode
 */
consensus_modules_t cmptr_pos_create_sha3_only_config(void);

/**
 * Verify PoS is using SHA3-only configuration
 * 
 * Checks that all modules use only SHA3 cryptography.
 * 
 * @param pos PoS state to verify
 * @return True if SHA3-only verified
 */
bool cmptr_pos_verify_sha3_only(const pos_state_v2_t* pos);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_POS_SHA3_CONFIG_H */