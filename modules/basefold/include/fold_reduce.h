#ifndef BASEFOLD_FOLD_REDUCE_H
#define BASEFOLD_FOLD_REDUCE_H

/**
 * @file fold_reduce.h
 * @brief BaseFold folding operations between SumCheck rounds
 * 
 * Implements the BaseFold protocol's oracle folding mechanism that reduces
 * the oracle size by half after each SumCheck phase. This includes computing
 * the folded Merkle tree and generating authentication paths.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "merkle/build.h"

/**
 * @brief Folded oracle structure
 * 
 * Contains the result of folding an oracle using a BaseFold challenge.
 * Each fold reduces the oracle size by half and produces a new Merkle tree.
 */
typedef struct {
    gf128_t *folded_codeword;       /**< Folded oracle data (half original size) */
    size_t folded_size;             /**< Size of folded codeword in GF(128) elements */
    merkle_tree_t tree;             /**< Merkle tree built from folded codeword */
    gf128_t fold_challenge;         /**< Challenge used for this fold */
    uint32_t fold_round;            /**< Round number (1 for first fold, 2 for second) */
    
    // Original codeword reference for frontier queries
    const gf128_t *original_codeword; /**< Reference to original codeword (not owned) */
    size_t original_size;           /**< Size of original codeword */
} folded_oracle_t;

/**
 * @brief Fold oracle using BaseFold protocol
 * 
 * @param original_codeword Original Reed-Muller codeword
 * @param original_size Size of original codeword in GF(128) elements
 * @param fold_challenge GF(128) challenge for folding
 * @param fold_round Round number (1 or 2)
 * @return Folded oracle structure or NULL on error
 * 
 * Performs BaseFold folding operation: for each pair (L,R) in the original
 * codeword, computes folded_val = L + challenge * R.
 * Builds new Merkle tree from the folded result.
 */
folded_oracle_t* fold_oracle(const gf128_t *original_codeword, size_t original_size,
                             gf128_t fold_challenge, uint32_t fold_round);

/**
 * @brief Generate frontier query for fold verification
 * 
 * @param oracle Folded oracle structure
 * @param query_index Index of folded element to open
 * @param auth_path_out Output buffer for authentication path (960 bytes)
 * @param original_left_out Output for left element from original oracle
 * @param original_right_out Output for right element from original oracle
 * @return 0 on success, -1 on error
 * 
 * Generates the "frontier query" proof that shows the fold was computed correctly.
 * Returns the two original elements and Merkle path that verify:
 * folded[query_index] = original_left + challenge * original_right
 */
int fold_generate_frontier_query(const folded_oracle_t *oracle, uint32_t query_index,
                                 uint8_t auth_path_out[960],
                                 gf128_t *original_left_out, gf128_t *original_right_out);

/**
 * @brief Verify frontier query for fold
 * 
 * @param folded_root Merkle root of folded oracle (32 bytes)
 * @param query_index Index being queried
 * @param auth_path Authentication path (960 bytes)
 * @param original_left Left element from original oracle
 * @param original_right Right element from original oracle
 * @param fold_challenge Challenge used for folding
 * @param full_leaf_group Complete 8-element leaf group for secure verification
 * @return 0 if verification passes, -1 if it fails
 * 
 * Verifies that:
 * 1. original_left + challenge * original_right matches the expected position in full_leaf_group
 * 2. Authentication path is valid against folded_root using the complete leaf group
 * 
 * SECURITY: Uses secure Merkle verification with complete leaf groups.
 */
int fold_verify_frontier_query(const uint8_t folded_root[32], uint32_t query_index,
                               const uint8_t auth_path[960],
                               gf128_t original_left, gf128_t original_right,
                               gf128_t fold_challenge,
                               const gf128_t full_leaf_group[8]);

/**
 * @brief Free folded oracle resources
 * 
 * @param oracle Folded oracle to free
 */
void fold_free_oracle(folded_oracle_t *oracle);

/**
 * @brief Compute folded value for testing
 * 
 * @param left Left element from original pair
 * @param right Right element from original pair  
 * @param challenge Fold challenge
 * @return Folded value: left + challenge * right
 * 
 * Helper function for testing fold correctness.
 */
gf128_t fold_compute_value(gf128_t left, gf128_t right, gf128_t challenge);

/**
 * @brief Print folded oracle summary
 * 
 * @param oracle Folded oracle to summarize
 */
void fold_print_summary(const folded_oracle_t *oracle);

#endif /* BASEFOLD_FOLD_REDUCE_H */