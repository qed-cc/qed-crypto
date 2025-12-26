#define _GNU_SOURCE  // For posix_memalign
#include "merkle/build.h"
#include "../../sha3/include/sha3.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

// Tree parameters - dynamically calculated based on input size
// The spec constants are for full d=18, but we support any size

// Memory management strategy: in-memory build
// Dynamic allocation based on actual tree size
#define MAX_TREE_DEPTH 20

static int allocate_tree_levels(merkle_tree_t *tree, uint32_t num_leaves) {
    // Calculate tree depth: ceil(log4(num_leaves))
    tree->depth = 0;
    uint32_t temp = num_leaves;
    while (temp > 1) {
        temp = (temp + 3) / 4;  // Ceiling division by 4
        tree->depth++;
    }
    
    if (tree->depth > MAX_TREE_DEPTH) {
        return -1;  // Tree too deep
    }
    
    // Allocate arrays for levels and sizes
    tree->levels = calloc(tree->depth + 1, sizeof(uint8_t*));
    tree->level_sizes = calloc(tree->depth + 1, sizeof(uint32_t));
    
    if (!tree->levels || !tree->level_sizes) {
        free(tree->levels);
        free(tree->level_sizes);
        tree->levels = NULL;
        tree->level_sizes = NULL;
        return -1;
    }
    
    // Allocate nodes per level for 4-ary tree
    uint32_t nodes_at_level = num_leaves;
    
    for (int level = 0; level <= tree->depth; ++level) {
        // SECURITY FIX: Check for integer overflow before multiplication
        if (nodes_at_level > SIZE_MAX / MERKLE_DIGEST_LEN) {
            fprintf(stderr, "Error: Integer overflow in level size calculation\n");
            merkle_tree_free(tree);
            return -1;
        }
        size_t level_size = nodes_at_level * MERKLE_DIGEST_LEN;
        // Round up to multiple of 64 for alignment
        size_t aligned_size = (level_size + 63) & ~63;
        tree->levels[level] = aligned_alloc(64, aligned_size);
        
        if (!tree->levels[level]) {
            merkle_tree_free(tree);
            return -1;
        }
        
        tree->level_sizes[level] = nodes_at_level;
        
        nodes_at_level = (nodes_at_level + 3) / 4;  // Ceiling division by 4
        if (nodes_at_level == 0) nodes_at_level = 1;  // Root level
    }
    
    return 0;
}

static void hash_leaf_group(const gf128_t *words, uint8_t *digest_out) {
    // SECURITY FIX: Add domain separation to prevent collision attacks
    // Format: domain_separator || leaf_data
    uint8_t leaf_data[129];  // 1 byte separator + 128 bytes data
    
    if (!words || !digest_out) {
        fprintf(stderr, "Error: NULL pointer in hash_leaf_group\n");
        return;
    }
    
    // SECURITY: Domain separator for leaf nodes
    leaf_data[0] = 0x00;  // Leaf domain
    
    // Inline the gf128_to_bytes conversions to avoid 1+ million function calls
    for (int i = 0; i < MERKLE_LEAF_WORDS; ++i) {
        uint8_t *out = leaf_data + 1 + i * 16;  // Offset by 1 for domain separator
        gf128_t a = words[i];
        
        // Inlined gf128_to_le
        out[0] = (uint8_t)(a.lo      );
        out[1] = (uint8_t)(a.lo >> 8 );
        out[2] = (uint8_t)(a.lo >> 16);
        out[3] = (uint8_t)(a.lo >> 24);
        out[4] = (uint8_t)(a.lo >> 32);
        out[5] = (uint8_t)(a.lo >> 40);
        out[6] = (uint8_t)(a.lo >> 48);
        out[7] = (uint8_t)(a.lo >> 56);
        out[8] = (uint8_t)(a.hi      );
        out[9] = (uint8_t)(a.hi >> 8 );
        out[10] = (uint8_t)(a.hi >> 16);
        out[11] = (uint8_t)(a.hi >> 24);
        out[12] = (uint8_t)(a.hi >> 32);
        out[13] = (uint8_t)(a.hi >> 40);
        out[14] = (uint8_t)(a.hi >> 48);
        out[15] = (uint8_t)(a.hi >> 56);
    }
    
    // Hash with SHA-3-256 including domain separator
    sha3_hash(SHA3_256, leaf_data, 129, digest_out, MERKLE_DIGEST_LEN);
}

static void hash_internal_node(const uint8_t *children, uint8_t *digest_out) {
    // SECURITY FIX: Add domain separation to prevent collision attacks
    // Format: domain_separator || child_digests
    uint8_t node_data[129];  // 1 byte separator + 128 bytes child digests
    
    if (!children || !digest_out) {
        fprintf(stderr, "Error: NULL pointer in hash_internal_node\n");
        return;
    }
    
    // SECURITY: Domain separator for internal nodes (different from leaves)
    node_data[0] = 0x01;  // Internal node domain
    
    // Copy 4 child digests (4 × 32 = 128 bytes)
    memcpy(node_data + 1, children, 4 * MERKLE_DIGEST_LEN);
    
    // Hash with SHA-3-256 including domain separator
    sha3_hash(SHA3_256, node_data, 129, digest_out, MERKLE_DIGEST_LEN);
}

/**
 * @brief Build a cryptographic Merkle tree from field elements
 * 
 * Constructs a 4-ary Merkle tree where each leaf contains 8 GF128 elements
 * and internal nodes are SHA3-256 hashes of their children. This tree
 * provides cryptographic commitments with efficient opening proofs.
 * 
 * SECURITY PROPERTIES:
 * - Collision Resistance: Finding two different codewords with same root
 *   requires breaking SHA3-256 (2^128 security)
 * - Binding: Cannot change committed values after building tree
 * - Authentication: Opening proofs are unforgeable
 * 
 * STRUCTURE:
 * - Leaf nodes: Groups of 8 field elements (128 bytes)
 * - Internal nodes: SHA3-256(child1 || child2 || child3 || child4)
 * - 4-ary tree: Each parent has up to 4 children
 * - Balanced: Depth = ceil(log4(num_leaves))
 * 
 * SECURITY CONSIDERATIONS:
 * - Integer overflow checks prevent memory corruption
 * - Zero-padding for incomplete groups prevents malleability
 * - Fixed ordering of children prevents reordering attacks
 * - All allocations checked for failure
 * 
 * @param code_word Array of field elements to commit (num_leaves * 8 elements)
 * @param num_leaves Number of leaf nodes (each contains 8 field elements)
 * @param tree Tree structure to initialize and build
 * @return 0 on success, -1 on error
 */
int merkle_build(const gf128_t *code_word, uint32_t num_leaves, merkle_tree_t *tree) {
    if (!code_word || !tree || num_leaves == 0) {
        return -1;
    }
    
    // Initialize tree structure
    memset(tree, 0, sizeof(merkle_tree_t));
    tree->leaves = num_leaves;
    
    // Allocate memory for all tree levels
    if (allocate_tree_levels(tree, num_leaves) != 0) {
        return -1;
    }
    
    // Step 1: Build leaf level (level 0)
    for (uint32_t i = 0; i < num_leaves; ++i) {
        hash_leaf_group(&code_word[i * MERKLE_LEAF_WORDS],
                       tree->levels[0] + i * MERKLE_DIGEST_LEN);
    }
    
    // Step 2: Build internal levels (level 1 to depth)
    uint32_t nodes_current = num_leaves;
    
    for (int level = 1; level <= tree->depth; ++level) {
        uint32_t nodes_parent = (nodes_current + 3) / 4;  // Ceiling division
        
        for (uint32_t i = 0; i < nodes_parent; ++i) {
            // Collect 4 children (or fewer for last group)
            uint8_t children[4 * MERKLE_DIGEST_LEN];
            memset(children, 0, sizeof(children));  // Zero-pad if needed
            
            uint32_t child_start = i * 4;
            uint32_t child_count = (child_start + 4 <= nodes_current) ? 4 : 
                                  (nodes_current - child_start);
            
            // Copy child digests in canonical order
            for (uint32_t j = 0; j < child_count; ++j) {
                memcpy(children + j * MERKLE_DIGEST_LEN,
                       tree->levels[level - 1] + (child_start + j) * MERKLE_DIGEST_LEN,
                       MERKLE_DIGEST_LEN);
            }
            
            // Hash parent node
            hash_internal_node(children, 
                              tree->levels[level] + i * MERKLE_DIGEST_LEN);
        }
        
        nodes_current = nodes_parent;
        if (nodes_current == 1) break;  // Reached root
    }
    
    // Copy root digest
    memcpy(tree->root, tree->levels[tree->depth], MERKLE_DIGEST_LEN);
    
    return 0;
}

int merkle_open(const merkle_tree_t *tree,
                const gf128_t *code_word,
                uint32_t idx,
                gf128_t *value_out,
                uint8_t *path) {
    if (!tree || !code_word || !value_out || !path) {
        return -1;
    }
    
    if (idx >= tree->leaves || !tree->levels) {
        return -1;  // Index out of bounds or tree not built
    }
    
    // Extract leaf value (the idx-th word of the codeword)
    // Note: idx represents the leaf index, each leaf contains 8 words
    // We return the first word of the leaf group for simplicity
    *value_out = code_word[idx * MERKLE_LEAF_WORDS];
    
    // Build authentication path
    uint32_t cur = idx;
    uint8_t *path_ptr = path;
    
    for (int level = 0; level < tree->depth; ++level) {
        uint32_t group = cur & ~3U;           // First child in group of 4
        uint32_t offset = cur & 3U;           // Position within group (0-3)
        
        // Copy all 4 sibling digests from this level
        uint8_t siblings[4 * MERKLE_DIGEST_LEN];
        uint32_t nodes_at_level = tree->level_sizes[level];
        
        for (int i = 0; i < 4; ++i) {
            uint32_t sibling_idx = group + i;
            if (sibling_idx < nodes_at_level) {  // Bounds check
                memcpy(siblings + i * MERKLE_DIGEST_LEN,
                       tree->levels[level] + sibling_idx * MERKLE_DIGEST_LEN,
                       MERKLE_DIGEST_LEN);
            } else {
                memset(siblings + i * MERKLE_DIGEST_LEN, 0, MERKLE_DIGEST_LEN);
            }
        }
        
        // Copy 3 siblings (excluding the one at our offset)
        int path_idx = 0;
        for (int i = 0; i < 4; ++i) {
            if (i != offset) {
                memcpy(path_ptr + path_idx * MERKLE_DIGEST_LEN,
                       siblings + i * MERKLE_DIGEST_LEN,
                       MERKLE_DIGEST_LEN);
                path_idx++;
            }
        }
        
        path_ptr += 3 * MERKLE_DIGEST_LEN;
        cur >>= 2;  // Move to parent index
    }
    
    return 0;
}

uint32_t merkle_path_size(const merkle_tree_t *tree) {
    return tree->depth * 3 * MERKLE_DIGEST_LEN;
}

void merkle_tree_free(merkle_tree_t *tree) {
    if (!tree) return;
    
    if (tree->levels) {
        for (uint32_t i = 0; i <= tree->depth; ++i) {
            free(tree->levels[i]);
        }
        free(tree->levels);
        tree->levels = NULL;
    }
    
    free(tree->level_sizes);
    tree->level_sizes = NULL;
    
    tree->depth = 0;
    tree->leaves = 0;
}
