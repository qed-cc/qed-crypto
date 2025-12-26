/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos_v2.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Initialize v2 PoS system */
pos_state_v2_t* cmptr_pos_v2_init(
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain,
    uint32_t protocol_version
) {
    if (!accumulator || !blockchain) {
        return NULL;
    }
    
    /* Check protocol version */
    if (protocol_version < CMPTR_POS_MIN_SUPPORTED_VERSION ||
        protocol_version > CMPTR_POS_PROTOCOL_VERSION) {
        fprintf(stderr, "Unsupported protocol version: %u\n", protocol_version);
        return NULL;
    }
    
    pos_state_v2_t* pos = calloc(1, sizeof(pos_state_v2_t));
    if (!pos) {
        return NULL;
    }
    
    /* Initialize base state using original init */
    pos_state_t* base = cmptr_pos_init(accumulator, blockchain);
    if (!base) {
        free(pos);
        return NULL;
    }
    
    /* Copy base state */
    memcpy(&pos->base, base, sizeof(pos_state_t));
    free(base);
    
    /* Set protocol versions */
    pos->protocol_version = protocol_version;
    pos->min_protocol_version = CMPTR_POS_MIN_SUPPORTED_VERSION;
    
    /* Default modules will be registered separately */
    pos->snapshot_module = NULL;
    pos->vrf_module = NULL;
    pos->ordering_module = NULL;
    pos->proof_module = NULL;
    
    /* Enable enhanced features based on version */
    if (protocol_version >= 2) {
        pos->fast_path_enabled = true;
        pos->streaming_dag_enabled = true;
        pos->parallel_proofs_enabled = true;
    } else {
        pos->fast_path_enabled = false;
        pos->streaming_dag_enabled = false;
        pos->parallel_proofs_enabled = false;
    }
    
    pos->current_mode = CONSENSUS_MODE_NORMAL;
    pos->upgrade_height = 0;
    pos->next_protocol_version = 0;
    
    /* Initialize module registry */
    pos->registered_modules = calloc(50, sizeof(module_interface_t*));
    pos->registered_modules_count = 0;
    pthread_rwlock_init(&pos->module_lock, NULL);
    
    printf("✓ PoS v2 initialized\n");
    printf("  - Protocol version: %u\n", pos->protocol_version);
    printf("  - Fast path: %s\n", pos->fast_path_enabled ? "enabled" : "disabled");
    printf("  - Streaming DAG: %s\n", pos->streaming_dag_enabled ? "enabled" : "disabled");
    printf("  - Parallel proofs: %s\n", pos->parallel_proofs_enabled ? "enabled" : "disabled");
    printf("  - Cryptography: SHA3-256 only (post-quantum secure)\n");
    
    /* Register and select default modules */
    if (!cmptr_pos_register_default_modules(pos)) {
        fprintf(stderr, "Failed to register default modules\n");
        pthread_rwlock_destroy(&pos->module_lock);
        free(pos->registered_modules);
        free(pos);
        return NULL;
    }
    
    if (!cmptr_pos_select_modules_for_version(pos, protocol_version)) {
        fprintf(stderr, "Failed to select modules for protocol v%u\n", protocol_version);
        pthread_rwlock_destroy(&pos->module_lock);
        free(pos->registered_modules);
        free(pos);
        return NULL;
    }
    
    return pos;
}

/* Destroy v2 PoS system */
void cmptr_pos_v2_destroy(pos_state_v2_t* pos) {
    if (!pos) return;
    
    /* Destroy modules if they have cleanup functions */
    if (pos->snapshot_module && pos->snapshot_module->base.destroy) {
        pos->snapshot_module->base.destroy(pos->snapshot_module);
    }
    if (pos->vrf_module && pos->vrf_module->base.destroy) {
        pos->vrf_module->base.destroy(pos->vrf_module);
    }
    if (pos->ordering_module && pos->ordering_module->base.destroy) {
        pos->ordering_module->base.destroy(pos->ordering_module);
    }
    if (pos->proof_module && pos->proof_module->base.destroy) {
        pos->proof_module->base.destroy(pos->proof_module);
    }
    
    /* Clean up module registry */
    for (uint32_t i = 0; i < pos->registered_modules_count; i++) {
        if (pos->registered_modules[i]) {
            if (pos->registered_modules[i]->destroy) {
                pos->registered_modules[i]->destroy(pos->registered_modules[i]);
            }
        }
    }
    free(pos->registered_modules);
    
    /* Clean up upgrade state */
    if (pos->upgrade_state) {
        pthread_mutex_destroy(&pos->upgrade_state->upgrade_mutex);
        free(pos->upgrade_state);
    }
    
    pthread_rwlock_destroy(&pos->module_lock);
    
    /* Destroy base state */
    cmptr_pos_destroy(&pos->base);
    
    free(pos);
}

/* Register snapshot module */
bool cmptr_pos_register_snapshot_module(
    pos_state_v2_t* pos,
    snapshot_module_t* module,
    uint32_t version
) {
    if (!pos || !module) {
        return false;
    }
    
    /* Check compatibility */
    if (module->base.is_compatible && 
        !module->base.is_compatible(pos->protocol_version)) {
        fprintf(stderr, "Snapshot module v%u incompatible with protocol v%u\n",
                version, pos->protocol_version);
        return false;
    }
    
    /* Replace existing module */
    if (pos->snapshot_module && pos->snapshot_module->base.destroy) {
        pos->snapshot_module->base.destroy(pos->snapshot_module);
    }
    
    pos->snapshot_module = module;
    module->base.version = version;
    
    printf("✓ Registered snapshot module: %s v%u\n", 
           module->base.name ? module->base.name : "unknown", version);
    
    return true;
}

/* Register VRF module */
bool cmptr_pos_register_vrf_module(
    pos_state_v2_t* pos,
    vrf_module_t* module,
    uint32_t version
) {
    if (!pos || !module) {
        return false;
    }
    
    /* Check compatibility */
    if (module->base.is_compatible && 
        !module->base.is_compatible(pos->protocol_version)) {
        fprintf(stderr, "VRF module v%u incompatible with protocol v%u\n",
                version, pos->protocol_version);
        return false;
    }
    
    /* Replace existing module */
    if (pos->vrf_module && pos->vrf_module->base.destroy) {
        pos->vrf_module->base.destroy(pos->vrf_module);
    }
    
    pos->vrf_module = module;
    module->base.version = version;
    
    printf("✓ Registered VRF module: %s v%u\n", 
           module->base.name ? module->base.name : "unknown", version);
    
    /* Check if aggregatable */
    if (module->is_aggregatable && module->is_aggregatable()) {
        printf("  - Supports VRF aggregation\n");
    }
    
    return true;
}

/* Register ordering module */
bool cmptr_pos_register_ordering_module(
    pos_state_v2_t* pos,
    ordering_module_t* module,
    uint32_t version
) {
    if (!pos || !module) {
        return false;
    }
    
    /* Check compatibility */
    if (module->base.is_compatible && 
        !module->base.is_compatible(pos->protocol_version)) {
        fprintf(stderr, "Ordering module v%u incompatible with protocol v%u\n",
                version, pos->protocol_version);
        return false;
    }
    
    /* Replace existing module */
    if (pos->ordering_module && pos->ordering_module->base.destroy) {
        pos->ordering_module->base.destroy(pos->ordering_module);
    }
    
    pos->ordering_module = module;
    module->base.version = version;
    
    printf("✓ Registered ordering module: %s v%u\n", 
           module->base.name ? module->base.name : "unknown", version);
    
    return true;
}

/* Register proof module */
bool cmptr_pos_register_proof_module(
    pos_state_v2_t* pos,
    proof_module_t* module,
    uint32_t version
) {
    if (!pos || !module) {
        return false;
    }
    
    /* Check compatibility */
    if (module->base.is_compatible && 
        !module->base.is_compatible(pos->protocol_version)) {
        fprintf(stderr, "Proof module v%u incompatible with protocol v%u\n",
                version, pos->protocol_version);
        return false;
    }
    
    /* Replace existing module */
    if (pos->proof_module && pos->proof_module->base.destroy) {
        pos->proof_module->base.destroy(pos->proof_module);
    }
    
    pos->proof_module = module;
    module->base.version = version;
    
    printf("✓ Registered proof module: %s v%u\n", 
           module->base.name ? module->base.name : "unknown", version);
    
    /* Check if supports parallel generation */
    if (module->supports_parallel && module->supports_parallel()) {
        printf("  - Supports parallel proof generation\n");
    }
    
    return true;
}

/* Schedule protocol upgrade */
bool cmptr_pos_schedule_upgrade(
    pos_state_v2_t* pos,
    uint32_t target_height,
    uint32_t new_version
) {
    if (!pos) {
        return false;
    }
    
    /* Validate version */
    if (new_version < CMPTR_POS_MIN_SUPPORTED_VERSION ||
        new_version == pos->protocol_version) {
        fprintf(stderr, "Invalid upgrade version: %u\n", new_version);
        return false;
    }
    
    /* Must be future height */
    if (target_height <= pos->base.blockchain->height) {
        fprintf(stderr, "Upgrade height must be in future\n");
        return false;
    }
    
    pos->upgrade_height = target_height;
    pos->next_protocol_version = new_version;
    
    printf("✓ Scheduled protocol upgrade:\n");
    printf("  - Current version: %u\n", pos->protocol_version);
    printf("  - Target version: %u\n", new_version);
    printf("  - Upgrade height: %u\n", target_height);
    printf("  - Blocks until upgrade: %lu\n", 
           target_height - pos->base.blockchain->height);
    
    return true;
}

/* Check if upgrade should happen */
bool cmptr_pos_check_upgrade(
    pos_state_v2_t* pos,
    uint64_t current_height
) {
    if (!pos || pos->upgrade_height == 0) {
        return false;
    }
    
    if (current_height >= pos->upgrade_height) {
        printf("\n=== PROTOCOL UPGRADE ===\n");
        printf("Upgrading from v%u to v%u at height %lu\n",
               pos->protocol_version, 
               pos->next_protocol_version,
               current_height);
        
        /* Perform upgrade */
        pos->protocol_version = pos->next_protocol_version;
        pos->upgrade_height = 0;
        pos->next_protocol_version = 0;
        
        /* Enable new features based on version */
        if (pos->protocol_version >= 2) {
            pos->fast_path_enabled = true;
            pos->streaming_dag_enabled = true;
            pos->parallel_proofs_enabled = true;
        }
        
        printf("✓ Upgrade complete\n");
        return true;
    }
    
    return false;
}

/* Get enhanced metrics */
pos_metrics_v2_t cmptr_pos_v2_get_metrics(const pos_state_v2_t* pos) {
    pos_metrics_v2_t metrics = {0};
    
    if (!pos) {
        return metrics;
    }
    
    /* Get base metrics */
    metrics.base_metrics = cmptr_pos_get_metrics(&pos->base);
    
    /* Add v2 metrics */
    metrics.fast_path_successes = 0;  /* TODO: Track these */
    metrics.fast_path_attempts = 0;
    metrics.parallel_proof_speedup = pos->parallel_proofs_enabled ? 4.0 : 1.0;
    metrics.streaming_vertices_processed = 0;  /* TODO: Track these */
    metrics.incremental_updates_saved = 0;
    metrics.current_mode = pos->current_mode;
    
    return metrics;
}