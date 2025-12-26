#ifndef MERKLE_BUILD_H
#define MERKLE_BUILD_H

#include <stdint.h>
#include "gf128.h"

#ifdef __cplusplus
extern "C" {
#endif

#define MERKLE_DIGEST_LEN 32     /* SHA-3-256 */
#define MERKLE_LEAF_WORDS 8      /* 8 × 16 B = 128 B */

/**
 * @brief Merkle tree structure for 4-ary tree with 32-byte digests
 * 
 * Represents a complete 4-ary Merkle tree built over a Reed-Muller codeword.
 * Each leaf contains 8 GF(2^128) words (128 bytes) hashed to 32 bytes.
 * Internal nodes hash 4 children (4×32=128 bytes) to 32 bytes.
 */
typedef struct {
    uint8_t root[MERKLE_DIGEST_LEN];  /**< Root digest (SHA-3-256) */
    uint32_t depth;                   /**< Tree depth (=10 for d=18) */
    uint32_t leaves;                  /**< Number of leaves (=1,048,576 for d=18) */
    uint8_t **levels;                 /**< Tree levels (dynamically allocated) */
    uint32_t *level_sizes;            /**< Number of nodes at each level */
} merkle_tree_t;

/**
 * @brief Build 4-ary Merkle tree from Reed-Muller codeword
 * 
 * @param code_word Input codeword array (8,388,608 words for d=18)
 * @param tree Output tree structure with root digest
 * @return 0 on success, -1 on error
 * 
 * Constructs a complete 4-ary Merkle tree where:
 * - Leaves: groups of 8 consecutive GF(128) words → SHA-3-256 digest
 * - Internal nodes: 4 child digests concatenated → SHA-3-256 digest
 * - Total SHA-3 calls: 1,398,101 for d=18
 * 
 * Memory usage: ~45 MiB for in-memory build, ≤2 MiB for streaming build
 */
/**
 * @brief Build 4-ary Merkle tree from Reed-Muller codeword
 * 
 * @param code_word Input codeword array (groups of GF128 words)
 * @param num_leaves Number of leaves (code_word length / MERKLE_LEAF_WORDS)
 * @param tree Output tree structure with root digest and leaf count
 * @return 0 on success, -1 on error
 */
int merkle_build(const gf128_t *code_word, uint32_t num_leaves, merkle_tree_t *tree);

/**
 * @brief Open Merkle leaf with authentication path
 * 
 * @param tree Tree structure from merkle_build()
 * @param code_word Original codeword (for leaf value extraction)
 * @param idx Leaf index (0 to leaves-1)
 * @param value_out Output leaf value (16 bytes)
 * @param path Output authentication path (30×32 = 960 bytes)
 * @return 0 on success, -1 on error
 * 
 * Returns the leaf value and its Merkle authentication path:
 * - value_out: The actual GF(128) word at the specified leaf
 * - path: 30 sibling digests (3 per level × 10 levels)
 * 
 * Path format: [level0_sib0, level0_sib1, level0_sib2, level1_sib0, ...]
 */
int merkle_open(const merkle_tree_t *tree,
                const gf128_t *code_word,
                uint32_t idx,
                gf128_t *value_out,
                uint8_t *path /* 30*32 B */);

/**
 * @brief Free Merkle tree resources
 * 
 * @param tree Tree structure to free
 */
void merkle_tree_free(merkle_tree_t *tree);

#ifdef __cplusplus
}
#endif

#endif // MERKLE_BUILD_H