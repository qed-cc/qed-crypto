/**
 * @file fold_reduce.c
 * @brief BaseFold folding operations implementation
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include "fold_reduce.h"
#include "merkle/verify.h"

gf128_t fold_compute_value(gf128_t left, gf128_t right, gf128_t challenge) {
    // BaseFold folding: folded = left + challenge * right
    gf128_t product = gf128_mul(challenge, right);
    return gf128_add(left, product);
}

folded_oracle_t* fold_oracle(const gf128_t *original_codeword, size_t original_size,
                             gf128_t fold_challenge, uint32_t fold_round) {
    if (!original_codeword || original_size == 0 || (original_size % 2) != 0) {
        return NULL;
    }
    
    folded_oracle_t *oracle = malloc(sizeof(folded_oracle_t));
    if (!oracle) return NULL;
    
    // Initialize structure
    oracle->folded_size = original_size / 2;
    oracle->fold_challenge = fold_challenge;
    oracle->fold_round = fold_round;
    oracle->folded_codeword = NULL;
    memset(&oracle->tree, 0, sizeof(merkle_tree_t));
    
    // Store reference to original codeword for frontier queries
    oracle->original_codeword = original_codeword;
    oracle->original_size = original_size;
    
    // Allocate folded codeword
    oracle->folded_codeword = malloc(oracle->folded_size * sizeof(gf128_t));
    if (!oracle->folded_codeword) {
        free(oracle);
        return NULL;
    }
    
    // Perform folding: for each pair (L,R), compute L + challenge * R
    for (size_t i = 0; i < oracle->folded_size; i++) {
        size_t left_idx = 2 * i;
        size_t right_idx = 2 * i + 1;
        
        gf128_t left = original_codeword[left_idx];
        gf128_t right = original_codeword[right_idx];
        
        oracle->folded_codeword[i] = fold_compute_value(left, right, fold_challenge);
    }
    
    // Build Merkle tree from folded codeword
    uint32_t num_leaves = (uint32_t)(oracle->folded_size / MERKLE_LEAF_WORDS);
    if (merkle_build(oracle->folded_codeword, num_leaves, &oracle->tree) != 0) {
        free(oracle->folded_codeword);
        free(oracle);
        return NULL;
    }
    
    return oracle;
}

int fold_generate_frontier_query(const folded_oracle_t *oracle, uint32_t query_index,
                                 uint8_t auth_path_out[960],
                                 gf128_t *original_left_out, gf128_t *original_right_out) {
    if (!oracle || !auth_path_out || !original_left_out || !original_right_out) {
        return -1;
    }
    
    if (query_index >= oracle->folded_size) {
        return -1;
    }
    
    // Validate access to original codeword
    if (!oracle->original_codeword || oracle->original_size == 0) {
        return -1;
    }
    
    // Generate Merkle opening for the folded value
    gf128_t opened_value;
    if (merkle_open(&oracle->tree, oracle->folded_codeword, query_index, 
                    &opened_value, auth_path_out) != 0) {
        return -1;
    }
    
    // Extract the original elements that were folded
    size_t original_left_idx = 2 * query_index;
    size_t original_right_idx = 2 * query_index + 1;
    
    // Bounds check
    if (original_right_idx >= oracle->original_size) {
        return -1;
    }
    
    // Return the original values used in folding
    *original_left_out = oracle->original_codeword[original_left_idx];
    *original_right_out = oracle->original_codeword[original_right_idx];
    
    // Validate the folding was computed correctly
    gf128_t expected_folded = fold_compute_value(*original_left_out, *original_right_out, 
                                                oracle->fold_challenge);
    if (!gf128_eq(expected_folded, oracle->folded_codeword[query_index])) {
        return -1;
    }
    
    return 0;
}

int fold_verify_frontier_query(const uint8_t folded_root[32], uint32_t query_index,
                               const uint8_t auth_path[960],
                               gf128_t original_left, gf128_t original_right,
                               gf128_t fold_challenge,
                               const gf128_t full_leaf_group[8]) {
    if (!folded_root || !auth_path || !full_leaf_group) {
        return -1;
    }
    
    // Compute expected folded value
    gf128_t expected_folded = fold_compute_value(original_left, original_right, fold_challenge);
    
    // Calculate which position within the leaf group this query corresponds to
    uint32_t leaf_group_idx = query_index / 8;
    uint32_t position_in_leaf = query_index % 8;
    
    // Verify that the expected value matches the provided leaf group
    if (!gf128_eq(expected_folded, full_leaf_group[position_in_leaf])) {
        return -1;  // Mismatch between expected and provided value
    }
    
    // Verify Merkle path using the complete leaf group (SECURE)
    return merkle_verify_leaf_group(folded_root, 10, leaf_group_idx, full_leaf_group, auth_path);
}

void fold_free_oracle(folded_oracle_t *oracle) {
    if (oracle) {
        free(oracle->folded_codeword);
        // Note: merkle_tree_t doesn't need explicit cleanup in current implementation
        free(oracle);
    }
}

void fold_print_summary(const folded_oracle_t *oracle) {
    if (!oracle) {
        printf("Folded Oracle: NULL\n");
        return;
    }
    
    printf("=== Folded Oracle Summary ===\n");
    printf("Fold round: %u\n", oracle->fold_round);
    printf("Folded size: %zu GF(128) elements\n", oracle->folded_size);
    printf("Folded size (MB): %.2f\n", (oracle->folded_size * 16.0) / (1024 * 1024));
    
    printf("Fold challenge: ");
    const uint8_t *challenge_bytes = (const uint8_t*)&oracle->fold_challenge;
    for (int i = 0; i < 8; i++) {
        printf("%02x", challenge_bytes[i]);
    }
    printf("...\n");
    
    printf("Merkle tree depth: %u\n", oracle->tree.depth);
    printf("Merkle tree leaves: %u\n", oracle->tree.leaves);
    
    printf("Merkle root: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", oracle->tree.root[i]);
    }
    printf("...\n");
    
    if (oracle->folded_size <= 16) {
        printf("First few folded values:\n");
        for (size_t i = 0; i < oracle->folded_size && i < 8; i++) {
            const uint8_t *val_bytes = (const uint8_t*)&oracle->folded_codeword[i];
            printf("  [%zu]: %02x%02x%02x%02x...\n", i, 
                   val_bytes[0], val_bytes[1], val_bytes[2], val_bytes[3]);
        }
    } else {
        printf("First 4 folded values:\n");
        for (size_t i = 0; i < 4; i++) {
            const uint8_t *val_bytes = (const uint8_t*)&oracle->folded_codeword[i];
            printf("  [%zu]: %02x%02x%02x%02x...\n", i, 
                   val_bytes[0], val_bytes[1], val_bytes[2], val_bytes[3]);
        }
        printf("  ... (%zu more)\n", oracle->folded_size - 4);
    }
}