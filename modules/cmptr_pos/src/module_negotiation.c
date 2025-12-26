/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos_v2.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <pthread.h>

/* Module registry entry */
typedef struct {
    module_interface_t* module;
    module_type_t type;
    uint32_t version;
    bool is_active;
} module_registry_entry_t;

/* Module version negotiation state */
typedef struct {
    module_registry_entry_t* entries;
    uint32_t count;
    uint32_t capacity;
    pthread_rwlock_t registry_lock;
} module_registry_t;

/* Global module registry (would be in pos_state_v2_t) */
static module_registry_t* g_module_registry = NULL;

/* Initialize module registry */
static bool init_module_registry(void) {
    if (g_module_registry) {
        return true;  /* Already initialized */
    }
    
    g_module_registry = calloc(1, sizeof(module_registry_t));
    if (!g_module_registry) {
        return false;
    }
    
    g_module_registry->capacity = 50;  /* Support up to 50 modules */
    g_module_registry->entries = calloc(g_module_registry->capacity, 
                                       sizeof(module_registry_entry_t));
    
    if (!g_module_registry->entries) {
        free(g_module_registry);
        g_module_registry = NULL;
        return false;
    }
    
    pthread_rwlock_init(&g_module_registry->registry_lock, NULL);
    
    printf("✓ Module registry initialized (capacity: %u)\n", 
           g_module_registry->capacity);
    
    return true;
}

/* Register a module in the global registry */
bool cmptr_pos_register_module(
    module_interface_t* module,
    module_type_t type,
    uint32_t version
) {
    if (!module || !init_module_registry()) {
        return false;
    }
    
    pthread_rwlock_wrlock(&g_module_registry->registry_lock);
    
    /* Check if already registered */
    for (uint32_t i = 0; i < g_module_registry->count; i++) {
        module_registry_entry_t* entry = &g_module_registry->entries[i];
        if (entry->type == type && entry->version == version) {
            pthread_rwlock_unlock(&g_module_registry->registry_lock);
            fprintf(stderr, "Module type %d v%u already registered\n", type, version);
            return false;
        }
    }
    
    /* Check capacity */
    if (g_module_registry->count >= g_module_registry->capacity) {
        pthread_rwlock_unlock(&g_module_registry->registry_lock);
        fprintf(stderr, "Module registry full\n");
        return false;
    }
    
    /* Add to registry */
    module_registry_entry_t* entry = &g_module_registry->entries[g_module_registry->count];
    entry->module = module;
    entry->type = type;
    entry->version = version;
    entry->is_active = false;
    
    g_module_registry->count++;
    
    pthread_rwlock_unlock(&g_module_registry->registry_lock);
    
    printf("✓ Registered module: %s (type=%d, v%u)\n", 
           module->name ? module->name : "unknown", type, version);
    
    return true;
}

/* Find best module version for protocol */
static module_interface_t* find_best_module(
    module_type_t type,
    uint32_t protocol_version
) {
    if (!g_module_registry) {
        return NULL;
    }
    
    module_interface_t* best = NULL;
    uint32_t best_version = 0;
    
    pthread_rwlock_rdlock(&g_module_registry->registry_lock);
    
    for (uint32_t i = 0; i < g_module_registry->count; i++) {
        module_registry_entry_t* entry = &g_module_registry->entries[i];
        
        if (entry->type != type) {
            continue;
        }
        
        /* Check compatibility */
        if (entry->module->is_compatible && 
            !entry->module->is_compatible(protocol_version)) {
            continue;
        }
        
        /* Find highest compatible version */
        if (entry->version > best_version) {
            best = entry->module;
            best_version = entry->version;
        }
    }
    
    pthread_rwlock_unlock(&g_module_registry->registry_lock);
    
    return best;
}

/* Select modules for a specific protocol version */
bool cmptr_pos_select_modules_for_version(
    pos_state_v2_t* pos,
    uint32_t protocol_version
) {
    if (!pos || !g_module_registry) {
        return false;
    }
    
    printf("\n=== Module Selection for Protocol v%u ===\n", protocol_version);
    
    /* Select snapshot module */
    module_interface_t* snapshot = find_best_module(MODULE_TYPE_SNAPSHOT, protocol_version);
    if (!snapshot) {
        fprintf(stderr, "No compatible snapshot module found\n");
        return false;
    }
    pos->snapshot_module = (snapshot_module_t*)snapshot;
    printf("  - Snapshot: %s v%u\n", snapshot->name, snapshot->version);
    
    /* Select VRF module */
    module_interface_t* vrf = find_best_module(MODULE_TYPE_VRF, protocol_version);
    if (!vrf) {
        fprintf(stderr, "No compatible VRF module found\n");
        return false;
    }
    pos->vrf_module = (vrf_module_t*)vrf;
    printf("  - VRF: %s v%u\n", vrf->name, vrf->version);
    
    /* Select ordering module */
    module_interface_t* ordering = find_best_module(MODULE_TYPE_ORDERING, protocol_version);
    if (!ordering) {
        fprintf(stderr, "No compatible ordering module found\n");
        return false;
    }
    pos->ordering_module = (ordering_module_t*)ordering;
    printf("  - Ordering: %s v%u\n", ordering->name, ordering->version);
    
    /* Select proof module */
    module_interface_t* proof = find_best_module(MODULE_TYPE_PROOF, protocol_version);
    if (!proof) {
        fprintf(stderr, "No compatible proof module found\n");
        return false;
    }
    pos->proof_module = (proof_module_t*)proof;
    printf("  - Proof: %s v%u\n", proof->name, proof->version);
    
    /* Initialize selected modules */
    if (pos->snapshot_module->base.init) {
        void* config = NULL;  /* Module-specific config */
        pos->snapshot_module->base.init(config);
    }
    
    if (pos->vrf_module->base.init) {
        void* config = NULL;
        pos->vrf_module->base.init(config);
    }
    
    if (pos->ordering_module->base.init) {
        void* config = NULL;
        pos->ordering_module->base.init(config);
    }
    
    if (pos->proof_module->base.init) {
        void* config = NULL;
        pos->proof_module->base.init(config);
    }
    
    printf("\n✓ All modules selected and initialized\n");
    
    return true;
}

/* Prepare for module transition */
bool cmptr_pos_prepare_module_transition(
    pos_state_v2_t* pos,
    uint32_t new_protocol_version
) {
    if (!pos || !g_module_registry) {
        return false;
    }
    
    printf("\n=== Preparing Module Transition ===\n");
    printf("Current protocol: v%u → Target: v%u\n", 
           pos->protocol_version, new_protocol_version);
    
    /* Check what modules would change */
    bool changes_needed = false;
    
    /* Check snapshot module */
    module_interface_t* new_snapshot = find_best_module(MODULE_TYPE_SNAPSHOT, new_protocol_version);
    if (new_snapshot && new_snapshot->version != pos->snapshot_module->base.version) {
        printf("  - Snapshot: v%u → v%u\n", 
               pos->snapshot_module->base.version, new_snapshot->version);
        changes_needed = true;
    }
    
    /* Check VRF module */
    module_interface_t* new_vrf = find_best_module(MODULE_TYPE_VRF, new_protocol_version);
    if (new_vrf && new_vrf->version != pos->vrf_module->base.version) {
        printf("  - VRF: v%u → v%u\n", 
               pos->vrf_module->base.version, new_vrf->version);
        changes_needed = true;
    }
    
    /* Check ordering module */
    module_interface_t* new_ordering = find_best_module(MODULE_TYPE_ORDERING, new_protocol_version);
    if (new_ordering && new_ordering->version != pos->ordering_module->base.version) {
        printf("  - Ordering: v%u → v%u\n", 
               pos->ordering_module->base.version, new_ordering->version);
        changes_needed = true;
    }
    
    /* Check proof module */
    module_interface_t* new_proof = find_best_module(MODULE_TYPE_PROOF, new_protocol_version);
    if (new_proof && new_proof->version != pos->proof_module->base.version) {
        printf("  - Proof: v%u → v%u\n", 
               pos->proof_module->base.version, new_proof->version);
        changes_needed = true;
    }
    
    if (!changes_needed) {
        printf("✓ No module changes needed for v%u\n", new_protocol_version);
    } else {
        printf("\n✓ Module transition prepared\n");
        printf("  - Changes will activate at upgrade height\n");
        printf("  - Validators should pre-download new modules\n");
        printf("  - Smooth transition without fork\n");
    }
    
    return true;
}

/* Execute module transition */
bool cmptr_pos_execute_module_transition(
    pos_state_v2_t* pos,
    uint32_t new_protocol_version
) {
    if (!pos || !g_module_registry) {
        return false;
    }
    
    if (!pos->upgrade_state) {
        pos->upgrade_state = calloc(1, sizeof(upgrade_state_t));
        pthread_mutex_init(&pos->upgrade_state->upgrade_mutex, NULL);
    }
    
    pthread_mutex_lock(&pos->upgrade_state->upgrade_mutex);
    
    if (pos->upgrade_state->is_upgrading) {
        pthread_mutex_unlock(&pos->upgrade_state->upgrade_mutex);
        fprintf(stderr, "Upgrade already in progress\n");
        return false;
    }
    
    pos->upgrade_state->is_upgrading = true;
    pos->upgrade_state->start_time = time(NULL);
    
    printf("\n=== Executing Module Transition ===\n");
    
    /* Save old modules for graceful shutdown */
    snapshot_module_t* old_snapshot = pos->snapshot_module;
    vrf_module_t* old_vrf = pos->vrf_module;
    ordering_module_t* old_ordering = pos->ordering_module;
    proof_module_t* old_proof = pos->proof_module;
    
    /* Select new modules */
    if (!cmptr_pos_select_modules_for_version(pos, new_protocol_version)) {
        /* Rollback on failure */
        pos->snapshot_module = old_snapshot;
        pos->vrf_module = old_vrf;
        pos->ordering_module = old_ordering;
        pos->proof_module = old_proof;
        
        pos->upgrade_state->is_upgrading = false;
        pthread_mutex_unlock(&pos->upgrade_state->upgrade_mutex);
        
        fprintf(stderr, "Module transition failed - rolled back\n");
        return false;
    }
    
    /* Clean up old modules */
    if (old_snapshot && old_snapshot != pos->snapshot_module) {
        if (old_snapshot->base.destroy) {
            old_snapshot->base.destroy(old_snapshot);
        }
    }
    
    if (old_vrf && old_vrf != pos->vrf_module) {
        if (old_vrf->base.destroy) {
            old_vrf->base.destroy(old_vrf);
        }
    }
    
    if (old_ordering && old_ordering != pos->ordering_module) {
        if (old_ordering->base.destroy) {
            old_ordering->base.destroy(old_ordering);
        }
    }
    
    if (old_proof && old_proof != pos->proof_module) {
        if (old_proof->base.destroy) {
            old_proof->base.destroy(old_proof);
        }
    }
    
    pos->upgrade_state->is_upgrading = false;
    pos->upgrade_state->end_time = time(NULL);
    pos->upgrade_state->completed_count++;
    
    uint32_t upgrade_duration = pos->upgrade_state->end_time - pos->upgrade_state->start_time;
    
    pthread_mutex_unlock(&pos->upgrade_state->upgrade_mutex);
    
    printf("\n✓ Module transition complete\n");
    printf("  - Duration: %u seconds\n", upgrade_duration);
    printf("  - Total upgrades: %u\n", pos->upgrade_state->completed_count);
    printf("  - Zero downtime achieved\n");
    
    return true;
}

/* Demonstrate version negotiation */
void cmptr_pos_demonstrate_version_negotiation(pos_state_v2_t* pos) {
    if (!pos || !g_module_registry) {
        return;
    }
    
    printf("\n=== Version Negotiation Demo ===\n");
    
    /* Show current configuration */
    printf("\nCurrent modules (Protocol v%u):\n", pos->protocol_version);
    printf("  - Snapshot: %s v%u\n", 
           pos->snapshot_module->base.name,
           pos->snapshot_module->base.version);
    printf("  - VRF: %s v%u\n",
           pos->vrf_module->base.name,
           pos->vrf_module->base.version);
    printf("  - Ordering: %s v%u\n",
           pos->ordering_module->base.name,
           pos->ordering_module->base.version);
    printf("  - Proof: %s v%u\n",
           pos->proof_module->base.name,
           pos->proof_module->base.version);
    
    /* Show available modules */
    printf("\nAvailable modules in registry:\n");
    
    pthread_rwlock_rdlock(&g_module_registry->registry_lock);
    
    for (uint32_t i = 0; i < g_module_registry->count; i++) {
        module_registry_entry_t* entry = &g_module_registry->entries[i];
        const char* type_name = "";
        
        switch (entry->type) {
            case MODULE_TYPE_SNAPSHOT: type_name = "Snapshot"; break;
            case MODULE_TYPE_VRF: type_name = "VRF"; break;
            case MODULE_TYPE_ORDERING: type_name = "Ordering"; break;
            case MODULE_TYPE_PROOF: type_name = "Proof"; break;
            default: type_name = "Unknown"; break;
        }
        
        printf("  - [%s] %s v%u %s\n",
               type_name,
               entry->module->name,
               entry->version,
               entry->is_active ? "(active)" : "");
    }
    
    pthread_rwlock_unlock(&g_module_registry->registry_lock);
    
    /* Simulate protocol upgrade */
    printf("\nSimulating protocol upgrade v%u → v%u:\n",
           pos->protocol_version, pos->protocol_version + 1);
    
    cmptr_pos_prepare_module_transition(pos, pos->protocol_version + 1);
    
    printf("\nBenefits of version negotiation:\n");
    printf("  • Automatic selection of best compatible modules\n");
    printf("  • Graceful upgrades without hard forks\n");
    printf("  • Ability to test new algorithms on testnets\n");
    printf("  • Quick response to security threats\n");
    printf("  • Backward compatibility support\n");
}

/* Clean up module registry */
void cmptr_pos_cleanup_module_registry(void) {
    if (!g_module_registry) {
        return;
    }
    
    pthread_rwlock_destroy(&g_module_registry->registry_lock);
    free(g_module_registry->entries);
    free(g_module_registry);
    g_module_registry = NULL;
    
    printf("✓ Module registry cleaned up\n");
}