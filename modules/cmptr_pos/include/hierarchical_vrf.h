/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_HIERARCHICAL_VRF_H
#define CMPTR_POS_HIERARCHICAL_VRF_H

#include <stdint.h>
#include <stdbool.h>
#include "basefold_raa.h"
#include "cmptr_pos_common_types.h"

/* VRF proof structure */
typedef struct {
    uint8_t proof_bytes[128];    /* VRF proof */
    uint8_t output[32];          /* VRF output hash */
    uint32_t validator_id;
    bool is_valid;
} vrf_proof_t;

/* Aggregate proof for internal nodes */
typedef struct {
    basefold_raa_proof_t* proof;  /* Proof of correct aggregation */
    uint32_t subtree_size;        /* Number of leaves in subtree */
    uint32_t max_depth;           /* Maximum depth of subtree */
    hash256_t subtree_commitment; /* Merkle commitment of subtree */
} aggregate_proof_t;

/* VRF tree node */
typedef struct vrf_tree_node {
    uint32_t level;          /* 0 = leaf, increases up tree */
    uint32_t index;          /* Position at this level */
    
    union {
        struct {
            uint32_t validator_id;
            vrf_proof_t vrf_proof;
        } leaf;
        
        struct {
            struct vrf_tree_node* left;
            struct vrf_tree_node* right;
            aggregate_proof_t agg_proof;
        } internal;
    } data;
    
    hash256_t commitment;    /* Merkle commitment of subtree */
    struct vrf_tree_node* parent;  /* Parent node (for updates) */
} vrf_tree_node_t;

/* Hierarchical VRF tree */
typedef struct {
    vrf_tree_node_t* root;
    uint32_t height;
    uint32_t validator_count;
    
    /* Leaf node array for O(1) access */
    vrf_tree_node_t** leaf_nodes;
    
    /* Level roots for efficient verification */
    hash256_t* level_roots;
    
    /* Update tracking */
    uint32_t* dirty_leaves;      /* Bitmap of modified leaves */
    uint32_t dirty_count;
    
    /* Performance stats */
    uint64_t total_aggregations;
    uint64_t total_updates;
    uint64_t total_verification_time_us;
} hierarchical_vrf_tree_t;

/* Tree operations */
hierarchical_vrf_tree_t* vrf_tree_create(uint32_t validator_count);
void vrf_tree_free(hierarchical_vrf_tree_t* tree);

/* Build tree from VRF proofs */
bool vrf_tree_build(
    hierarchical_vrf_tree_t* tree,
    vrf_proof_t* proofs,
    uint32_t count
);

/* Update single validator's VRF proof */
bool vrf_tree_update(
    hierarchical_vrf_tree_t* tree,
    uint32_t validator_id,
    vrf_proof_t* new_proof
);

/* Batch update multiple validators */
bool vrf_tree_batch_update(
    hierarchical_vrf_tree_t* tree,
    uint32_t* validator_ids,
    vrf_proof_t* new_proofs,
    uint32_t count
);

/* Verify entire tree (O(1) with root proof) */
bool vrf_tree_verify(
    hierarchical_vrf_tree_t* tree,
    hash256_t expected_root
);

/* Get aggregated proof for validator subset */
aggregate_proof_t* vrf_tree_get_subset_proof(
    hierarchical_vrf_tree_t* tree,
    uint32_t* validator_ids,
    uint32_t count
);

/* Path verification for single validator */
typedef struct {
    vrf_proof_t leaf_proof;
    hash256_t siblings[32];      /* Merkle path siblings */
    uint32_t path_length;
    aggregate_proof_t* root_proof;
} vrf_membership_proof_t;

vrf_membership_proof_t* vrf_tree_get_membership_proof(
    hierarchical_vrf_tree_t* tree,
    uint32_t validator_id
);

bool vrf_tree_verify_membership(
    vrf_membership_proof_t* proof,
    uint32_t validator_id,
    hash256_t root_commitment
);

/* Performance statistics */
typedef struct {
    double avg_aggregation_time_ms;
    double avg_update_time_ms;
    double avg_verification_time_ms;
    uint32_t total_aggregations;
    uint32_t total_updates;
    double space_efficiency;  /* Actual size / naive size */
} vrf_tree_stats_t;

vrf_tree_stats_t vrf_tree_get_stats(hierarchical_vrf_tree_t* tree);

/* Utility functions */
bool verify_vrf_proof(vrf_proof_t* proof);
bool verify_aggregate_proof(aggregate_proof_t* proof);
uint32_t get_tree_height(uint32_t leaf_count);

#endif /* CMPTR_POS_HIERARCHICAL_VRF_H */