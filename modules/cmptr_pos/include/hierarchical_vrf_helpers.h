/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_HIERARCHICAL_VRF_HELPERS_H
#define CMPTR_POS_HIERARCHICAL_VRF_HELPERS_H

#include "hierarchical_vrf.h"
#include "pos_optimization_configs.h"

/* VRF update structure */
typedef struct {
    uint32_t validator_id;
    uint64_t new_stake;
} vrf_update_t;

/* Create VRF tree from config */
static inline hierarchical_vrf_tree_t* vrf_tree_create_with_config(vrf_tree_config_t* config) {
    if (!config) return NULL;
    return vrf_tree_create(config->initial_validators);
}

/* Overload for convenience */
#define vrf_tree_create(...) \
    _Generic((void*)(__VA_ARGS__), \
        vrf_tree_config_t*: vrf_tree_create_with_config, \
        default: vrf_tree_create \
    )(__VA_ARGS__)

/* Get root proof from tree */
static inline aggregate_proof_t* vrf_tree_get_root_proof(hierarchical_vrf_tree_t* tree) {
    if (!tree || !tree->root) return NULL;
    
    if (tree->root->level == 0) {
        /* Leaf node, no aggregate proof */
        return NULL;
    }
    
    return &tree->root->data.internal.agg_proof;
}

/* Batch update with stake changes */
static inline bool vrf_tree_batch_update_stakes(
    hierarchical_vrf_tree_t* tree,
    vrf_update_t* updates,
    uint32_t count
) {
    if (!tree || !updates) return false;
    
    /* For now, just mark validators as updated */
    /* In real implementation, would update VRF proofs based on new stakes */
    for (uint32_t i = 0; i < count; i++) {
        if (updates[i].validator_id < tree->validator_count) {
            /* Mark as needing update */
            vrf_tree_update(tree, updates[i].validator_id, NULL);
        }
    }
    
    return true;
}

/* Destroy VRF tree */
static inline void vrf_tree_destroy(hierarchical_vrf_tree_t* tree) {
    vrf_tree_free(tree);
}

#endif /* CMPTR_POS_HIERARCHICAL_VRF_HELPERS_H */