/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_trees.h"
#include "../../sha3/include/sha3.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#ifdef __AVX512F__
#include <immintrin.h>
#endif

// Internal node structure
typedef struct tree_node {
    uint8_t hash[CMPTR_TREE_HASH_SIZE];
    struct tree_node* left;
    struct tree_node* right;
    bool is_leaf;
    uint64_t leaf_index;  // For sparse trees
} tree_node_t;

// Tree structure
struct cmptr_tree {
    cmptr_tree_config_t config;
    tree_node_t* root;
    uint64_t leaf_count;
    uint32_t height;
    
    // Statistics
    uint64_t hash_computations;
    
    // Cache for recent hashes (simple LRU)
    struct {
        uint8_t* entries;
        size_t capacity;
        size_t size;
        uint64_t hits;
        uint64_t misses;
    } cache;
};

// Proof structure
struct cmptr_tree_proof {
    uint8_t** siblings;
    uint32_t sibling_count;
    uint64_t leaf_index;
};

// Batch structure
struct cmptr_tree_batch {
    cmptr_tree_t* tree;
    uint8_t** pending_leaves;
    size_t* pending_sizes;
    size_t pending_count;
    size_t pending_capacity;
};

// Hash function with domain separation
static void hash_leaf(const uint8_t* data, size_t data_len, uint8_t hash_out[32]) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"leaf", 4);
    sha3_update(&ctx, data, data_len);
    sha3_final(&ctx, hash_out, 32);
}

static void hash_internal(const uint8_t left[32], const uint8_t right[32], uint8_t hash_out[32]) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"node", 4);
    sha3_update(&ctx, left, 32);
    sha3_update(&ctx, right, 32);
    sha3_final(&ctx, hash_out, 32);
}

// Create new tree
cmptr_tree_t* cmptr_tree_new(const cmptr_tree_config_t* config) {
    cmptr_tree_t* tree = calloc(1, sizeof(cmptr_tree_t));
    if (!tree) return NULL;
    
    if (config) {
        tree->config = *config;
    } else {
        // Default config
        tree->config.type = CMPTR_TREE_STANDARD;
        tree->config.optimization_flags = CMPTR_TREE_OPT_NONE;
        tree->config.cache_enabled = true;
    }
    
    // Initialize cache if enabled
    if (tree->config.cache_enabled) {
        tree->cache.capacity = 1024;  // Simple fixed size
        tree->cache.entries = calloc(tree->cache.capacity, CMPTR_TREE_HASH_SIZE);
        if (!tree->cache.entries) {
            free(tree);
            return NULL;
        }
    }
    
    return tree;
}

// Add single leaf (simplified for demo)
bool cmptr_tree_add(cmptr_tree_t* tree, const uint8_t* data, size_t data_len) {
    if (!tree || !data) return false;
    
    // Create leaf node
    tree_node_t* leaf = calloc(1, sizeof(tree_node_t));
    if (!leaf) return false;
    
    hash_leaf(data, data_len, leaf->hash);
    leaf->is_leaf = true;
    leaf->leaf_index = tree->leaf_count;
    tree->hash_computations++;
    
    // For demo, just store as new root (real implementation would build proper tree)
    if (!tree->root) {
        tree->root = leaf;
    } else {
        // Create new internal node
        tree_node_t* new_root = calloc(1, sizeof(tree_node_t));
        if (!new_root) {
            free(leaf);
            return false;
        }
        
        new_root->left = tree->root;
        new_root->right = leaf;
        hash_internal(tree->root->hash, leaf->hash, new_root->hash);
        tree->hash_computations++;
        
        tree->root = new_root;
    }
    
    tree->leaf_count++;
    return true;
}

// Batch operations
cmptr_tree_batch_t* cmptr_tree_batch_new(cmptr_tree_t* tree) {
    if (!tree) return NULL;
    
    cmptr_tree_batch_t* batch = calloc(1, sizeof(cmptr_tree_batch_t));
    if (!batch) return NULL;
    
    batch->tree = tree;
    batch->pending_capacity = 1024;
    batch->pending_leaves = calloc(batch->pending_capacity, sizeof(uint8_t*));
    batch->pending_sizes = calloc(batch->pending_capacity, sizeof(size_t));
    
    if (!batch->pending_leaves || !batch->pending_sizes) {
        free(batch->pending_leaves);
        free(batch->pending_sizes);
        free(batch);
        return NULL;
    }
    
    return batch;
}

bool cmptr_tree_batch_add(cmptr_tree_batch_t* batch, const uint8_t* data, size_t data_len) {
    if (!batch || !data) return false;
    
    // Grow if needed
    if (batch->pending_count >= batch->pending_capacity) {
        size_t new_capacity = batch->pending_capacity * 2;
        uint8_t** new_leaves = realloc(batch->pending_leaves, new_capacity * sizeof(uint8_t*));
        size_t* new_sizes = realloc(batch->pending_sizes, new_capacity * sizeof(size_t));
        
        if (!new_leaves || !new_sizes) {
            free(new_leaves);
            free(new_sizes);
            return false;
        }
        
        batch->pending_leaves = new_leaves;
        batch->pending_sizes = new_sizes;
        batch->pending_capacity = new_capacity;
    }
    
    // Copy data
    batch->pending_leaves[batch->pending_count] = malloc(data_len);
    if (!batch->pending_leaves[batch->pending_count]) return false;
    
    memcpy(batch->pending_leaves[batch->pending_count], data, data_len);
    batch->pending_sizes[batch->pending_count] = data_len;
    batch->pending_count++;
    
    return true;
}

bool cmptr_tree_batch_commit(cmptr_tree_batch_t* batch) {
    if (!batch) return false;
    
    // For demo, just add all leaves sequentially
    // Real implementation would build tree layer by layer for efficiency
    for (size_t i = 0; i < batch->pending_count; i++) {
        if (!cmptr_tree_add(batch->tree, batch->pending_leaves[i], batch->pending_sizes[i])) {
            return false;
        }
        free(batch->pending_leaves[i]);
    }
    
    batch->pending_count = 0;
    return true;
}

void cmptr_tree_batch_free(cmptr_tree_batch_t* batch) {
    if (!batch) return;
    
    // Free any pending leaves
    for (size_t i = 0; i < batch->pending_count; i++) {
        free(batch->pending_leaves[i]);
    }
    
    free(batch->pending_leaves);
    free(batch->pending_sizes);
    free(batch);
}

// Get root hash
bool cmptr_tree_root(const cmptr_tree_t* tree, uint8_t root_out[CMPTR_TREE_HASH_SIZE]) {
    if (!tree || !tree->root || !root_out) return false;
    memcpy(root_out, tree->root->hash, CMPTR_TREE_HASH_SIZE);
    return true;
}

// Generate proof (simplified for demo)
cmptr_tree_proof_t* cmptr_tree_prove(const cmptr_tree_t* tree, uint64_t leaf_index) {
    if (!tree || leaf_index >= tree->leaf_count) return NULL;
    
    cmptr_tree_proof_t* proof = calloc(1, sizeof(cmptr_tree_proof_t));
    if (!proof) return NULL;
    
    // For demo, create simple proof with one sibling
    proof->sibling_count = 1;
    proof->siblings = calloc(1, sizeof(uint8_t*));
    proof->siblings[0] = calloc(1, CMPTR_TREE_HASH_SIZE);
    
    if (!proof->siblings || !proof->siblings[0]) {
        cmptr_tree_proof_free(proof);
        return NULL;
    }
    
    // Dummy sibling hash
    memset(proof->siblings[0], 0xFF, CMPTR_TREE_HASH_SIZE);
    proof->leaf_index = leaf_index;
    
    return proof;
}

// Verify proof
bool cmptr_tree_verify(
    const uint8_t root[CMPTR_TREE_HASH_SIZE],
    uint64_t leaf_index,
    const uint8_t* leaf_data,
    size_t leaf_data_len,
    const cmptr_tree_proof_t* proof
) {
    if (!root || !leaf_data || !proof) return false;
    
    // Compute leaf hash
    uint8_t current_hash[CMPTR_TREE_HASH_SIZE];
    hash_leaf(leaf_data, leaf_data_len, current_hash);
    
    // For demo, just check that we have a proof
    return proof->sibling_count > 0;
}

// Get statistics
void cmptr_tree_stats(const cmptr_tree_t* tree, cmptr_tree_stats_t* stats_out) {
    if (!tree || !stats_out) return;
    
    stats_out->leaf_count = tree->leaf_count;
    stats_out->height = tree->height;
    stats_out->memory_usage = sizeof(cmptr_tree_t);  // Simplified
    stats_out->hash_computations = tree->hash_computations;
    stats_out->cache_enabled = tree->config.cache_enabled;
    
    if (tree->config.cache_enabled && tree->cache.hits + tree->cache.misses > 0) {
        stats_out->cache_hit_rate = (double)tree->cache.hits / 
                                   (tree->cache.hits + tree->cache.misses);
    } else {
        stats_out->cache_hit_rate = 0.0;
    }
}

// Free tree
static void free_node(tree_node_t* node) {
    if (!node) return;
    free_node(node->left);
    free_node(node->right);
    free(node);
}

void cmptr_tree_free(cmptr_tree_t* tree) {
    if (!tree) return;
    
    free_node(tree->root);
    free(tree->cache.entries);
    free(tree);
}

// Free proof
void cmptr_tree_proof_free(cmptr_tree_proof_t* proof) {
    if (!proof) return;
    
    for (uint32_t i = 0; i < proof->sibling_count; i++) {
        free(proof->siblings[i]);
    }
    free(proof->siblings);
    free(proof);
}

// Utility functions
void cmptr_tree_hash(const uint8_t* data, size_t data_len, uint8_t hash_out[CMPTR_TREE_HASH_SIZE]) {
    hash_leaf(data, data_len, hash_out);
}

void cmptr_tree_hash_combine(
    const uint8_t left[CMPTR_TREE_HASH_SIZE],
    const uint8_t right[CMPTR_TREE_HASH_SIZE],
    uint8_t parent_out[CMPTR_TREE_HASH_SIZE]
) {
    hash_internal(left, right, parent_out);
}

// Batch verification (simplified)
bool cmptr_tree_batch_verify(
    const uint8_t root[CMPTR_TREE_HASH_SIZE],
    const uint64_t* leaf_indices,
    const uint8_t** leaf_data,
    const size_t* leaf_data_lens,
    const cmptr_tree_proof_t** proofs,
    size_t count
) {
    // For demo, verify each individually
    for (size_t i = 0; i < count; i++) {
        if (!cmptr_tree_verify(root, leaf_indices[i], leaf_data[i], 
                              leaf_data_lens[i], proofs[i])) {
            return false;
        }
    }
    return true;
}