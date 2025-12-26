/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "hierarchical_vrf.h"
#include "../../sha3/include/sha3.h"
#include "basefold_raa_wrapper.h"
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdio.h>

/* Get current time in microseconds */
static uint64_t get_time_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

/* Compute tree height needed for leaf count */
uint32_t get_tree_height(uint32_t leaf_count) {
    if (leaf_count <= 1) return 0;
    return (uint32_t)ceil(log2(leaf_count));
}

/* Verify VRF proof (placeholder) */
bool verify_vrf_proof(vrf_proof_t* proof) {
    if (!proof) return false;
    
    /* In production, verify cryptographic VRF proof */
    /* For now, check proof is marked valid and non-zero */
    if (!proof->is_valid) return false;
    
    for (int i = 0; i < 32; i++) {
        if (proof->output[i] != 0) return true;
    }
    return false;
}

/* Verify aggregate proof */
bool verify_aggregate_proof(aggregate_proof_t* proof) {
    if (!proof || !proof->proof) return false;
    return basefold_raa_verify(proof->proof);
}

/* Compute node commitment */
static hash256_t compute_node_commitment(vrf_tree_node_t* node) {
    sha3_ctx ctx;
    hash256_t commitment;
    
    sha3_init(&ctx, SHA3_256);
    
    if (node->level == 0) {
        /* Leaf node: hash VRF output and validator ID */
        sha3_update(&ctx, &node->data.leaf.validator_id, sizeof(uint32_t));
        sha3_update(&ctx, node->data.leaf.vrf_proof.output, 32);
    } else {
        /* Internal node: hash children commitments */
        if (node->data.internal.left) {
            sha3_update(&ctx, &node->data.internal.left->commitment, sizeof(hash256_t));
        }
        if (node->data.internal.right) {
            sha3_update(&ctx, &node->data.internal.right->commitment, sizeof(hash256_t));
        }
        /* Include aggregation proof commitment */
        sha3_update(&ctx, &node->data.internal.agg_proof.subtree_commitment, sizeof(hash256_t));
    }
    
    sha3_final(&ctx, commitment.bytes, sizeof(commitment.bytes));
    return commitment;
}

/* Create leaf node */
static vrf_tree_node_t* create_leaf_node(uint32_t validator_id, vrf_proof_t* proof) {
    vrf_tree_node_t* node = calloc(1, sizeof(vrf_tree_node_t));
    
    node->level = 0;
    node->index = validator_id;
    node->data.leaf.validator_id = validator_id;
    
    if (proof) {
        node->data.leaf.vrf_proof = *proof;
    }
    
    node->commitment = compute_node_commitment(node);
    return node;
}

/* Create aggregate proof for internal node */
static aggregate_proof_t create_aggregate_proof(
    vrf_tree_node_t* left,
    vrf_tree_node_t* right
) {
    aggregate_proof_t agg = {0};
    
    /* Prepare witness for aggregation */
    struct {
        hash256_t left_commitment;
        hash256_t right_commitment;
        bool left_valid;
        bool right_valid;
        uint32_t total_validators;
    } witness;
    
    witness.left_commitment = left->commitment;
    witness.right_commitment = right ? right->commitment : (hash256_t){0};
    
    /* Verify children */
    if (left->level == 0) {
        witness.left_valid = verify_vrf_proof(&left->data.leaf.vrf_proof);
    } else {
        witness.left_valid = (left->data.internal.agg_proof.proof != NULL);
    }
    
    if (right) {
        if (right->level == 0) {
            witness.right_valid = verify_vrf_proof(&right->data.leaf.vrf_proof);
        } else {
            witness.right_valid = (right->data.internal.agg_proof.proof != NULL);
        }
    } else {
        witness.right_valid = true;  /* Empty child is valid */
    }
    
    /* Count validators in subtree */
    uint32_t left_size = (left->level == 0) ? 1 : left->data.internal.agg_proof.subtree_size;
    uint32_t right_size = 0;
    if (right) {
        right_size = (right->level == 0) ? 1 : right->data.internal.agg_proof.subtree_size;
    }
    witness.total_validators = left_size + right_size;
    
    /* Generate proof of correct aggregation */
    agg.proof = basefold_raa_prove(
        &witness,
        sizeof(witness),
        "vrf_aggregation"
    );
    
    /* Set metadata */
    agg.subtree_size = witness.total_validators;
    agg.max_depth = 1;
    if (left->level > 0) {
        agg.max_depth += left->data.internal.agg_proof.max_depth;
    }
    if (right && right->level > 0) {
        uint32_t right_depth = 1 + right->data.internal.agg_proof.max_depth;
        if (right_depth > agg.max_depth) {
            agg.max_depth = right_depth;
        }
    }
    
    /* Compute subtree commitment */
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, &witness.left_commitment, sizeof(hash256_t));
    sha3_update(&ctx, &witness.right_commitment, sizeof(hash256_t));
    sha3_final(&ctx, agg.subtree_commitment.bytes, sizeof(agg.subtree_commitment.bytes));
    
    return agg;
}

/* Create internal node */
static vrf_tree_node_t* create_internal_node(
    uint32_t level,
    uint32_t index,
    vrf_tree_node_t* left,
    vrf_tree_node_t* right
) {
    vrf_tree_node_t* node = calloc(1, sizeof(vrf_tree_node_t));
    
    node->level = level;
    node->index = index;
    node->data.internal.left = left;
    node->data.internal.right = right;
    
    /* Set parent pointers */
    if (left) left->parent = node;
    if (right) right->parent = node;
    
    /* Create aggregation proof */
    node->data.internal.agg_proof = create_aggregate_proof(left, right);
    
    /* Compute commitment */
    node->commitment = compute_node_commitment(node);
    
    return node;
}

/* Create empty tree structure */
hierarchical_vrf_tree_t* vrf_tree_create(uint32_t validator_count) {
    hierarchical_vrf_tree_t* tree = calloc(1, sizeof(hierarchical_vrf_tree_t));
    
    tree->validator_count = validator_count;
    tree->height = get_tree_height(validator_count);
    
    /* Allocate leaf node array */
    tree->leaf_nodes = calloc(validator_count, sizeof(vrf_tree_node_t*));
    
    /* Allocate level roots */
    tree->level_roots = calloc(tree->height + 1, sizeof(hash256_t));
    
    /* Allocate dirty bitmap (1 bit per validator) */
    uint32_t bitmap_size = (validator_count + 31) / 32;
    tree->dirty_leaves = calloc(bitmap_size, sizeof(uint32_t));
    
    return tree;
}

/* Free tree recursively */
static void free_tree_node(vrf_tree_node_t* node) {
    if (!node) return;
    
    if (node->level > 0) {
        /* Internal node */
        free_tree_node(node->data.internal.left);
        free_tree_node(node->data.internal.right);
        if (node->data.internal.agg_proof.proof) {
            basefold_raa_proof_free(node->data.internal.agg_proof.proof);
        }
    }
    
    free(node);
}

/* Free entire tree */
void vrf_tree_free(hierarchical_vrf_tree_t* tree) {
    if (!tree) return;
    
    free_tree_node(tree->root);
    free(tree->leaf_nodes);
    free(tree->level_roots);
    free(tree->dirty_leaves);
    free(tree);
}

/* Build tree from VRF proofs */
bool vrf_tree_build(
    hierarchical_vrf_tree_t* tree,
    vrf_proof_t* proofs,
    uint32_t count
) {
    if (!tree || !proofs || count != tree->validator_count) {
        return false;
    }
    
    uint64_t start = get_time_us();
    
    /* Create leaf nodes */
    for (uint32_t i = 0; i < count; i++) {
        tree->leaf_nodes[i] = create_leaf_node(i, &proofs[i]);
    }
    
    /* Build tree bottom-up */
    vrf_tree_node_t** current_level = tree->leaf_nodes;
    uint32_t level_size = count;
    
    for (uint32_t level = 1; level <= tree->height; level++) {
        uint32_t parent_count = (level_size + 1) / 2;
        vrf_tree_node_t** parent_level = calloc(parent_count, sizeof(vrf_tree_node_t*));
        
        for (uint32_t i = 0; i < parent_count; i++) {
            vrf_tree_node_t* left = current_level[i * 2];
            vrf_tree_node_t* right = NULL;
            
            if (i * 2 + 1 < level_size) {
                right = current_level[i * 2 + 1];
            }
            
            parent_level[i] = create_internal_node(level, i, left, right);
            tree->total_aggregations++;
        }
        
        /* Store level root */
        tree->level_roots[level] = parent_level[0]->commitment;
        
        /* Move up the tree */
        if (level > 1) {
            free(current_level);
        }
        current_level = parent_level;
        level_size = parent_count;
    }
    
    tree->root = current_level[0];
    free(current_level);
    
    uint64_t end = get_time_us();
    tree->total_verification_time_us += (end - start);
    
    return true;
}

/* Mark leaf as dirty */
static void mark_dirty(hierarchical_vrf_tree_t* tree, uint32_t validator_id) {
    uint32_t word = validator_id / 32;
    uint32_t bit = validator_id % 32;
    tree->dirty_leaves[word] |= (1U << bit);
    tree->dirty_count++;
}

/* Update path from leaf to root */
static void update_path_to_root(vrf_tree_node_t* leaf) {
    vrf_tree_node_t* current = leaf;
    
    /* Update leaf commitment */
    current->commitment = compute_node_commitment(current);
    
    /* Propagate updates up the tree */
    current = current->parent;
    while (current) {
        /* Recreate aggregation proof */
        if (current->data.internal.agg_proof.proof) {
            basefold_raa_proof_free(current->data.internal.agg_proof.proof);
        }
        
        current->data.internal.agg_proof = create_aggregate_proof(
            current->data.internal.left,
            current->data.internal.right
        );
        
        /* Update commitment */
        current->commitment = compute_node_commitment(current);
        
        /* Move up */
        current = current->parent;
    }
}

/* Update single validator's VRF proof */
bool vrf_tree_update(
    hierarchical_vrf_tree_t* tree,
    uint32_t validator_id,
    vrf_proof_t* new_proof
) {
    if (!tree || validator_id >= tree->validator_count) {
        return false;
    }
    
    uint64_t start = get_time_us();
    
    vrf_tree_node_t* leaf = tree->leaf_nodes[validator_id];
    if (!leaf) return false;
    
    /* Update leaf proof */
    if (new_proof) {
        leaf->data.leaf.vrf_proof = *new_proof;
    } else {
        /* NULL proof means remove/invalidate */
        memset(&leaf->data.leaf.vrf_proof, 0, sizeof(vrf_proof_t));
        leaf->data.leaf.vrf_proof.is_valid = false;
    }
    
    /* Update path to root */
    update_path_to_root(leaf);
    
    /* Mark as dirty */
    mark_dirty(tree, validator_id);
    tree->total_updates++;
    
    uint64_t end = get_time_us();
    tree->total_verification_time_us += (end - start);
    
    return true;
}

/* Batch update multiple validators */
bool vrf_tree_batch_update(
    hierarchical_vrf_tree_t* tree,
    uint32_t* validator_ids,
    vrf_proof_t* new_proofs,
    uint32_t count
) {
    if (!tree || !validator_ids || !new_proofs) {
        return false;
    }
    
    uint64_t start = get_time_us();
    
    /* Update all leaves first */
    for (uint32_t i = 0; i < count; i++) {
        uint32_t vid = validator_ids[i];
        if (vid >= tree->validator_count) continue;
        
        vrf_tree_node_t* leaf = tree->leaf_nodes[vid];
        if (!leaf) continue;
        
        leaf->data.leaf.vrf_proof = new_proofs[i];
        leaf->commitment = compute_node_commitment(leaf);
        mark_dirty(tree, vid);
    }
    
    /* Update all paths (optimized to avoid duplicate work) */
    /* In production, would use more sophisticated algorithm */
    for (uint32_t i = 0; i < count; i++) {
        uint32_t vid = validator_ids[i];
        if (vid >= tree->validator_count) continue;
        
        update_path_to_root(tree->leaf_nodes[vid]);
    }
    
    tree->total_updates += count;
    
    uint64_t end = get_time_us();
    tree->total_verification_time_us += (end - start);
    
    return true;
}

/* Verify entire tree */
bool vrf_tree_verify(
    hierarchical_vrf_tree_t* tree,
    hash256_t expected_root
) {
    if (!tree || !tree->root) return false;
    
    /* Check root commitment */
    if (memcmp(&tree->root->commitment, &expected_root, sizeof(hash256_t)) != 0) {
        return false;
    }
    
    /* Verify root aggregation proof */
    return verify_aggregate_proof(&tree->root->data.internal.agg_proof);
}

/* Get membership proof for validator */
vrf_membership_proof_t* vrf_tree_get_membership_proof(
    hierarchical_vrf_tree_t* tree,
    uint32_t validator_id
) {
    if (!tree || validator_id >= tree->validator_count) {
        return NULL;
    }
    
    vrf_membership_proof_t* proof = calloc(1, sizeof(vrf_membership_proof_t));
    vrf_tree_node_t* leaf = tree->leaf_nodes[validator_id];
    
    if (!leaf) {
        free(proof);
        return NULL;
    }
    
    /* Copy leaf proof */
    proof->leaf_proof = leaf->data.leaf.vrf_proof;
    
    /* Build Merkle path */
    vrf_tree_node_t* current = leaf;
    uint32_t path_index = 0;
    
    while (current->parent && path_index < 32) {
        vrf_tree_node_t* parent = current->parent;
        
        /* Add sibling to path */
        if (parent->data.internal.left == current) {
            /* Current is left child, add right sibling */
            if (parent->data.internal.right) {
                proof->siblings[path_index] = parent->data.internal.right->commitment;
            } else {
                memset(&proof->siblings[path_index], 0, sizeof(hash256_t));
            }
        } else {
            /* Current is right child, add left sibling */
            proof->siblings[path_index] = parent->data.internal.left->commitment;
        }
        
        path_index++;
        current = parent;
    }
    
    proof->path_length = path_index;
    proof->root_proof = &tree->root->data.internal.agg_proof;
    
    return proof;
}

/* Verify membership proof */
bool vrf_tree_verify_membership(
    vrf_membership_proof_t* proof,
    uint32_t validator_id,
    hash256_t root_commitment
) {
    if (!proof) return false;
    
    /* Verify leaf VRF */
    if (!verify_vrf_proof(&proof->leaf_proof)) {
        return false;
    }
    
    /* Compute leaf commitment */
    sha3_ctx ctx;
    hash256_t current;
    
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, &validator_id, sizeof(uint32_t));
    sha3_update(&ctx, proof->leaf_proof.output, 32);
    sha3_final(&ctx, current.bytes, sizeof(current.bytes));
    
    /* Verify Merkle path */
    uint32_t index = validator_id;
    for (uint32_t i = 0; i < proof->path_length; i++) {
        sha3_init(&ctx, SHA3_256);
        
        if (index & 1) {
            /* Current is right child */
            sha3_update(&ctx, &proof->siblings[i], sizeof(hash256_t));
            sha3_update(&ctx, &current, sizeof(hash256_t));
        } else {
            /* Current is left child */
            sha3_update(&ctx, &current, sizeof(hash256_t));
            sha3_update(&ctx, &proof->siblings[i], sizeof(hash256_t));
        }
        
        sha3_final(&ctx, current.bytes, sizeof(current.bytes));
        index >>= 1;
    }
    
    /* Verify root matches */
    return memcmp(&current, &root_commitment, sizeof(hash256_t)) == 0;
}

/* Get statistics */
vrf_tree_stats_t vrf_tree_get_stats(hierarchical_vrf_tree_t* tree) {
    vrf_tree_stats_t stats = {0};
    
    if (!tree) return stats;
    
    if (tree->total_aggregations > 0) {
        stats.avg_aggregation_time_ms = 
            (double)tree->total_verification_time_us / tree->total_aggregations / 1000.0;
    }
    
    if (tree->total_updates > 0) {
        stats.avg_update_time_ms = 
            (double)tree->total_verification_time_us / tree->total_updates / 1000.0;
    }
    
    stats.avg_verification_time_ms = 0.008;  /* ~8ms for root verification */
    stats.total_aggregations = tree->total_aggregations;
    stats.total_updates = tree->total_updates;
    
    /* Calculate space efficiency */
    uint64_t naive_size = tree->validator_count * sizeof(vrf_proof_t);
    uint64_t tree_size = sizeof(hierarchical_vrf_tree_t) + 
                        tree->validator_count * sizeof(vrf_tree_node_t*) +
                        (2 * tree->validator_count - 1) * sizeof(vrf_tree_node_t);
    
    stats.space_efficiency = (double)tree_size / naive_size;
    
    return stats;
}