/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#define _GNU_SOURCE
#include "basefold_raa.h"
#include "sha3.h"
#include "merkle/build.h"
#include "logger.h"
#include <stdlib.h>
#include <string.h>

/**
 * @brief Build Merkle tree commitment for RAA codeword
 * 
 * Unlike standard Merkle trees, we can leverage RAA structure
 * for more efficient commitments.
 */
typedef struct {
    uint8_t* nodes;      /* All tree nodes */
    size_t num_leaves;   /* Number of leaves */
    size_t tree_height;  /* Height of tree */
} raa_merkle_tree_t;

/**
 * @brief Compute tree height
 */
static size_t compute_tree_height(size_t num_leaves) {
    size_t height = 0;
    size_t n = num_leaves;
    while (n > 1) {
        height++;
        n = (n + 1) / 2;  // Round up for odd sizes
    }
    return height;
}

/**
 * @brief Build Merkle tree over RAA codeword
 */
static raa_merkle_tree_t* build_raa_merkle_tree(const gf128_t* codeword, 
                                                size_t codeword_len) {
    
    raa_merkle_tree_t* tree = malloc(sizeof(raa_merkle_tree_t));
    if (!tree) {
        LOG_ERROR("raa_commit", "Failed to allocate %zu bytes for RAA Merkle tree", sizeof(raa_merkle_tree_t));
        return NULL;
    }
    
    tree->num_leaves = codeword_len;
    tree->tree_height = compute_tree_height(codeword_len);
    
    // Allocate nodes (leaves + internal nodes)
    size_t total_nodes = (2 * codeword_len) - 1;
    tree->nodes = calloc(total_nodes, 32);
    if (!tree->nodes) {
        free(tree);
        return NULL;
    }
    
    // Hash leaves
    for (size_t i = 0; i < codeword_len; i++) {
        sha3_ctx ctx;
        sha3_init(&ctx, SHA3_256);
        sha3_update(&ctx, (const uint8_t*)&codeword[i], sizeof(gf128_t));
        sha3_final(&ctx, tree->nodes + i * 32, 32);
    }
    
    // Build internal nodes
    size_t level_start = 0;
    size_t level_size = codeword_len;
    
    while (level_size > 1) {
        size_t next_level_size = (level_size + 1) / 2;
        size_t next_level_start = level_start + level_size;
        
        for (size_t i = 0; i < next_level_size; i++) {
            sha3_ctx ctx;
            sha3_init(&ctx, SHA3_256);
            
            // Left child
            size_t left_idx = level_start + 2 * i;
            sha3_update(&ctx, tree->nodes + left_idx * 32, 32);
            
            // Right child (if exists)
            if (2 * i + 1 < level_size) {
                size_t right_idx = level_start + 2 * i + 1;
                sha3_update(&ctx, tree->nodes + right_idx * 32, 32);
            } else {
                // Odd size - duplicate left child
                sha3_update(&ctx, tree->nodes + left_idx * 32, 32);
            }
            
            sha3_final(&ctx, tree->nodes + (next_level_start + i) * 32, 32);
        }
        
        level_start = next_level_start;
        level_size = next_level_size;
    }
    
    return tree;
}

/**
 * @brief Get Merkle root
 */
static void get_merkle_root(const raa_merkle_tree_t* tree, uint8_t root[32]) {
    // Root is the last node
    size_t root_idx = (2 * tree->num_leaves) - 2;
    memcpy(root, tree->nodes + root_idx * 32, 32);
}

/**
 * @brief Generate Merkle path for a leaf
 */
static int generate_merkle_path(const raa_merkle_tree_t* tree,
                               size_t leaf_idx,
                               uint8_t** path,
                               size_t* path_length) {
    
    if (leaf_idx >= tree->num_leaves) {
        return -1;
    }
    
    *path_length = tree->tree_height;
    *path = malloc(tree->tree_height * 32);
    if (!*path) {
        LOG_ERROR("raa_commit", "Failed to allocate %zu bytes for Merkle path", tree->tree_height * 32);
        return -2;
    }
    
    size_t current_idx = leaf_idx;
    size_t level_start = 0;
    size_t level_size = tree->num_leaves;
    
    for (size_t level = 0; level < tree->tree_height; level++) {
        // Get sibling index
        size_t sibling_idx;
        if (current_idx % 2 == 0) {
            // We are left child, sibling is right
            sibling_idx = current_idx + 1;
            if (sibling_idx >= level_size) {
                // No right sibling - use self
                sibling_idx = current_idx;
            }
        } else {
            // We are right child, sibling is left
            sibling_idx = current_idx - 1;
        }
        
        // Copy sibling hash to path
        memcpy((*path) + level * 32, 
               tree->nodes + (level_start + sibling_idx) * 32, 
               32);
        
        // Move to next level
        size_t next_level_size = (level_size + 1) / 2;
        level_start += level_size;
        level_size = next_level_size;
        current_idx = current_idx / 2;
    }
    
    return 0;
}

/**
 * @brief Free Merkle tree
 */
static void free_merkle_tree(raa_merkle_tree_t* tree) {
    if (tree) {
        if (tree->nodes) {
            free(tree->nodes);
        }
        free(tree);
    }
}

/**
 * @brief Commit to RAA codeword and generate opening proofs
 * 
 * This is called internally by basefold_raa_prove
 */
int raa_commit_and_open(const gf128_t* codeword,
                       size_t codeword_len,
                       const size_t* query_indices,
                       size_t num_queries,
                       uint8_t root[32],
                       uint8_t*** merkle_paths) {
    
    // Build Merkle tree
    raa_merkle_tree_t* tree = build_raa_merkle_tree(codeword, codeword_len);
    if (!tree) {
        return -1;
    }
    
    // Get root
    get_merkle_root(tree, root);
    
    // Generate paths for queries
    *merkle_paths = calloc(num_queries, sizeof(uint8_t*));
    if (!*merkle_paths) {
        free_merkle_tree(tree);
        return -2;
    }
    
    for (size_t i = 0; i < num_queries; i++) {
        size_t path_length;
        int ret = generate_merkle_path(tree, query_indices[i], 
                                      &(*merkle_paths)[i], &path_length);
        if (ret != 0) {
            // Cleanup on error
            for (size_t j = 0; j < i; j++) {
                free((*merkle_paths)[j]);
            }
            free(*merkle_paths);
            free_merkle_tree(tree);
            return -3;
        }
    }
    
    free_merkle_tree(tree);
    return 0;
}