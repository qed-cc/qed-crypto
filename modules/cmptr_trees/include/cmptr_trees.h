/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_TREES_H
#define CMPTR_TREES_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Constants
#define CMPTR_TREE_HASH_SIZE    32   // SHA3-256
#define CMPTR_TREE_MAX_HEIGHT   64   // Support up to 2^64 leaves

// Tree types
typedef enum {
    CMPTR_TREE_STANDARD = 0,     // Standard Merkle tree
    CMPTR_TREE_SPARSE,           // Sparse Merkle tree
    CMPTR_TREE_VERKLE            // Verkle tree (constant size proofs)
} cmptr_tree_type_t;

// Optimization hints
typedef enum {
    CMPTR_TREE_OPT_NONE = 0,
    CMPTR_TREE_OPT_BATCH = 1,      // Optimize for batch operations
    CMPTR_TREE_OPT_STREAMING = 2,  // Optimize for streaming updates
    CMPTR_TREE_OPT_PROOF_SIZE = 4, // Optimize for smaller proofs
    CMPTR_TREE_OPT_VERIFY_SPEED = 8 // Optimize for fast verification
} cmptr_tree_opt_t;

// Forward declarations
typedef struct cmptr_tree cmptr_tree_t;
typedef struct cmptr_tree_proof cmptr_tree_proof_t;
typedef struct cmptr_tree_batch cmptr_tree_batch_t;

// Tree configuration
typedef struct {
    cmptr_tree_type_t type;
    uint32_t optimization_flags;  // Bitmask of cmptr_tree_opt_t
    uint32_t leaf_count_hint;     // Expected number of leaves
    bool cache_enabled;           // Enable internal caching
} cmptr_tree_config_t;

// Create new tree
cmptr_tree_t* cmptr_tree_new(const cmptr_tree_config_t* config);

// Add single leaf
bool cmptr_tree_add(
    cmptr_tree_t* tree,
    const uint8_t* data,
    size_t data_len
);

// Batch operations for efficiency
cmptr_tree_batch_t* cmptr_tree_batch_new(cmptr_tree_t* tree);

bool cmptr_tree_batch_add(
    cmptr_tree_batch_t* batch,
    const uint8_t* data,
    size_t data_len
);

bool cmptr_tree_batch_commit(cmptr_tree_batch_t* batch);
void cmptr_tree_batch_free(cmptr_tree_batch_t* batch);

// Get root hash
bool cmptr_tree_root(
    const cmptr_tree_t* tree,
    uint8_t root_out[CMPTR_TREE_HASH_SIZE]
);

// Generate inclusion proof
cmptr_tree_proof_t* cmptr_tree_prove(
    const cmptr_tree_t* tree,
    uint64_t leaf_index
);

// Verify inclusion proof
bool cmptr_tree_verify(
    const uint8_t root[CMPTR_TREE_HASH_SIZE],
    uint64_t leaf_index,
    const uint8_t* leaf_data,
    size_t leaf_data_len,
    const cmptr_tree_proof_t* proof
);

// Batch verification (more efficient)
bool cmptr_tree_batch_verify(
    const uint8_t root[CMPTR_TREE_HASH_SIZE],
    const uint64_t* leaf_indices,
    const uint8_t** leaf_data,
    const size_t* leaf_data_lens,
    const cmptr_tree_proof_t** proofs,
    size_t count
);

// Update existing leaf
bool cmptr_tree_update(
    cmptr_tree_t* tree,
    uint64_t leaf_index,
    const uint8_t* new_data,
    size_t new_data_len
);

// Get tree statistics
typedef struct {
    uint64_t leaf_count;
    uint32_t height;
    size_t memory_usage;
    uint64_t hash_computations;
    bool cache_enabled;
    double cache_hit_rate;
} cmptr_tree_stats_t;

void cmptr_tree_stats(
    const cmptr_tree_t* tree,
    cmptr_tree_stats_t* stats_out
);

// Proof serialization
bool cmptr_tree_proof_export(
    const cmptr_tree_proof_t* proof,
    uint8_t* out,
    size_t* out_len
);

cmptr_tree_proof_t* cmptr_tree_proof_import(
    const uint8_t* data,
    size_t data_len
);

// Advanced: Range proofs (prove multiple leaves efficiently)
cmptr_tree_proof_t* cmptr_tree_prove_range(
    const cmptr_tree_t* tree,
    uint64_t start_index,
    uint64_t end_index  // Exclusive
);

// Advanced: Sparse tree operations
bool cmptr_tree_sparse_set(
    cmptr_tree_t* tree,
    uint64_t index,
    const uint8_t* value,
    size_t value_len
);

bool cmptr_tree_sparse_get(
    const cmptr_tree_t* tree,
    uint64_t index,
    uint8_t* value_out,
    size_t* value_len
);

// Free resources
void cmptr_tree_free(cmptr_tree_t* tree);
void cmptr_tree_proof_free(cmptr_tree_proof_t* proof);

// Utility: Hash arbitrary data
void cmptr_tree_hash(
    const uint8_t* data,
    size_t data_len,
    uint8_t hash_out[CMPTR_TREE_HASH_SIZE]
);

// Utility: Combine two hashes (for manual tree building)
void cmptr_tree_hash_combine(
    const uint8_t left[CMPTR_TREE_HASH_SIZE],
    const uint8_t right[CMPTR_TREE_HASH_SIZE],
    uint8_t parent_out[CMPTR_TREE_HASH_SIZE]
);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_TREES_H