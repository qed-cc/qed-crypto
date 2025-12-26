/**
 * @file merkle_commitment.c
 * @brief Implementation of Merkle tree commitment openings
 */

#include "merkle_commitment.h"
#include "merkle/build.h"  // For merkle_open function and MERKLE_LEAF_WORDS
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

/**
 * @brief Get authentication path for a leaf
 * 
 * The authentication path consists of all sibling hashes from leaf to root
 */
static int get_auth_path(
    const merkle_tree_t* tree,
    uint32_t leaf_index,
    uint8_t* auth_path,
    size_t* path_len)
{
    if (!tree || !auth_path || !path_len) {
        return -1;
    }
    
    // Calculate path length (log2 of number of leaves)
    uint32_t num_leaves = tree->leaves;
    size_t depth = 0;
    uint32_t temp = num_leaves;
    while (temp > 1) {
        temp >>= 1;
        depth++;
    }
    
    *path_len = depth * 32; // 32 bytes per hash
    
    // Build authentication path from leaf to root
    uint32_t current_index = leaf_index;
    size_t offset = 0;
    
    // Start from leaf level
    for (size_t level = 0; level < depth; level++) {
        // Determine sibling index
        uint32_t sibling_index;
        if (current_index % 2 == 0) {
            sibling_index = current_index + 1;
        } else {
            sibling_index = current_index - 1;
        }
        
        // Get sibling hash from tree structure
        // This is a simplified version - actual implementation would
        // need to access the tree's internal node structure
        
        // For now, create a dummy sibling hash
        // TODO: Access actual tree structure
        memset(auth_path + offset, 0xAB, 32);
        offset += 32;
        
        // Move up to parent
        current_index /= 2;
    }
    
    return 0;
}

int merkle_create_opening_with_codeword(
    const merkle_tree_t* tree,
    const gf128_t* codeword,
    size_t codeword_size,
    uint32_t leaf_index,
    merkle_opening_t* opening)
{
    if (!tree || !codeword || !opening || leaf_index >= tree->leaves) {
        return -1;
    }
    
    opening->leaf_index = leaf_index;
    
    // SECURITY FIX: Extract actual leaf values from codeword
    // Each leaf contains 8 consecutive GF128 elements
    size_t base_idx = leaf_index * MERKLE_LEAF_WORDS;
    if (base_idx + MERKLE_LEAF_WORDS - 1 >= codeword_size) {
        fprintf(stderr, "Error: Leaf index %u out of bounds for codeword size %zu\n", 
                leaf_index, codeword_size);
        return -1;
    }
    
    // Copy all 8 field elements for this leaf
    for (int i = 0; i < MERKLE_LEAF_WORDS; ++i) {
        opening->leaf_values[i] = codeword[base_idx + i];
    }
    
    // Allocate space for authentication path
    // For a 4-ary tree, we need 3 siblings per level * tree depth * 32 bytes per hash
    size_t path_len = 3 * tree->depth * MERKLE_DIGEST_LEN;
    opening->auth_path = malloc(path_len);
    if (!opening->auth_path) {
        return -1;
    }
    opening->path_len = path_len;
    
    // SECURITY FIX: Use the actual merkle_open function to get authentication path
    // We need to pass the first word of the leaf group for the value
    gf128_t leaf_value;
    int result = merkle_open(tree, codeword, leaf_index, &leaf_value, opening->auth_path);
    if (result != 0) {
        free(opening->auth_path);
        opening->auth_path = NULL;
        return -1;
    }
    
    return 0;
}

// Keep old function for compatibility but mark as deprecated
int merkle_create_opening(
    const merkle_tree_t* tree,
    uint32_t leaf_index,
    merkle_opening_t* opening)
{
    // Deprecated: Use merkle_create_opening_with_codeword instead
    if (!tree || !opening || leaf_index >= tree->leaves) {
        return -1;
    }
    
    opening->leaf_index = leaf_index;
    memset(opening->leaf_values, 0, 4 * sizeof(gf128_t));
    
    size_t path_len = 3 * tree->depth * MERKLE_DIGEST_LEN;
    opening->auth_path = malloc(path_len);
    if (!opening->auth_path) {
        return -1;
    }
    opening->path_len = path_len;
    memset(opening->auth_path, 0, path_len);
    
    return 0;
}

int merkle_create_sumcheck_openings(
    const merkle_tree_t* tree,
    const gf128_t* eval_point,
    size_t num_vars,
    merkle_commitment_proof_t* proof)
{
    if (!tree || !eval_point || !proof) {
        return -1;
    }
    
    // Initialize proof structure
    memcpy(proof->root, tree->root, 32);
    
    // For sumcheck final evaluation, we typically need to open
    // the polynomial at the evaluation point
    // Since we're using multilinear polynomials over boolean hypercube,
    // we need to determine which leaf corresponds to the evaluation point
    
    // If eval_point is in {0,1}^n, convert to leaf index
    uint32_t leaf_index = merkle_point_to_leaf_index(eval_point, num_vars);
    
    // For now, create a single opening
    // In practice, we might need multiple openings for batched verification
    proof->num_openings = 1;
    proof->openings = malloc(sizeof(merkle_opening_t*));
    if (!proof->openings) {
        return -1;
    }
    
    proof->openings[0] = malloc(sizeof(merkle_opening_t));
    if (!proof->openings[0]) {
        free(proof->openings);
        return -1;
    }
    
    // Create the opening
    if (merkle_create_opening(tree, leaf_index, proof->openings[0]) != 0) {
        free(proof->openings[0]);
        free(proof->openings);
        return -1;
    }
    
    return 0;
}

bool merkle_verify_opening(
    const merkle_opening_t* opening,
    const uint8_t root[32])
{
    if (!opening || !root || !opening->auth_path) {
        return false;
    }
    
    // SECURITY FIX: Verify the full leaf group (8 values)
    
    // Calculate tree depth from path length
    // For 4-ary tree: each level needs 3 siblings * 32 bytes
    uint32_t depth = opening->path_len / (3 * 32);
    
    // Use the secure leaf group verification
    int result = merkle_verify_leaf_group(
        root,                           // Expected root
        depth,                          // Tree depth
        opening->leaf_index,            // Leaf index
        opening->leaf_values,           // All 8 GF128 values in the leaf
        opening->auth_path              // Authentication path
    );
    
    return (result == 0);  // Convert to bool: true if verification succeeded
}

bool merkle_verify_commitment_proof(
    const merkle_commitment_proof_t* proof)
{
    if (!proof || !proof->openings) {
        return false;
    }
    
    // Verify each opening
    for (size_t i = 0; i < proof->num_openings; i++) {
        if (!merkle_verify_opening(proof->openings[i], proof->root)) {
            return false;
        }
    }
    
    return true;
}

int merkle_serialize_commitment_proof(
    const merkle_commitment_proof_t* proof,
    uint8_t* buffer,
    size_t buffer_size)
{
    if (!proof || !buffer) {
        return -1;
    }
    
    size_t offset = 0;
    
    // Write root
    if (offset + 32 > buffer_size) return -1;
    memcpy(buffer + offset, proof->root, 32);
    offset += 32;
    
    // Write number of openings
    if (offset + 4 > buffer_size) return -1;
    uint32_t num_openings = proof->num_openings;
    memcpy(buffer + offset, &num_openings, 4);
    offset += 4;
    
    // Write each opening
    for (size_t i = 0; i < proof->num_openings; i++) {
        merkle_opening_t* opening = proof->openings[i];
        
        // Write leaf index
        if (offset + 4 > buffer_size) return -1;
        memcpy(buffer + offset, &opening->leaf_index, 4);
        offset += 4;
        
        // Write leaf values (8 * 16 bytes)
        if (offset + 128 > buffer_size) return -1;
        for (int j = 0; j < 8; j++) {
            memcpy(buffer + offset, &opening->leaf_values[j], 16);
            offset += 16;
        }
        
        // Write path length
        if (offset + 4 > buffer_size) return -1;
        uint32_t path_len = opening->path_len;
        memcpy(buffer + offset, &path_len, 4);
        offset += 4;
        
        // Write authentication path
        if (offset + opening->path_len > buffer_size) return -1;
        memcpy(buffer + offset, opening->auth_path, opening->path_len);
        offset += opening->path_len;
    }
    
    return offset;
}

int merkle_deserialize_commitment_proof(
    const uint8_t* buffer,
    size_t buffer_size,
    merkle_commitment_proof_t* proof)
{
    if (!buffer || !proof) {
        return -1;
    }
    
    // Initialize the proof structure to ensure clean state
    memset(proof, 0, sizeof(merkle_commitment_proof_t));
    
    size_t offset = 0;
    
    // Read root
    if (offset + 32 > buffer_size) return -1;
    memcpy(proof->root, buffer + offset, 32);
    offset += 32;
    
    // Read number of openings
    if (offset + 4 > buffer_size) return -1;
    memcpy(&proof->num_openings, buffer + offset, 4);
    offset += 4;
    
    // Sanity check number of openings
    if (proof->num_openings == 0 || proof->num_openings > 1000000) {
        return -1;
    }
    
    // Allocate openings array
    proof->openings = calloc(proof->num_openings, sizeof(merkle_opening_t*));
    if (!proof->openings) {
        return -1;
    }
    
    // Read each opening
    for (size_t i = 0; i < proof->num_openings; i++) {
        proof->openings[i] = calloc(1, sizeof(merkle_opening_t));
        if (!proof->openings[i]) {
            // Clean up on error
            for (size_t j = 0; j < i; j++) {
                if (proof->openings[j]) {
                    free(proof->openings[j]->auth_path);
                    free(proof->openings[j]);
                }
            }
            free(proof->openings);
            proof->openings = NULL;
            proof->num_openings = 0;
            return -1;
        }
        
        merkle_opening_t* opening = proof->openings[i];
        
        // Read leaf index
        if (offset + 4 > buffer_size) return -1;
        memcpy(&opening->leaf_index, buffer + offset, 4);
        offset += 4;
        
        // Read leaf values
        if (offset + 128 > buffer_size) return -1;
        for (int j = 0; j < 8; j++) {
            memcpy(&opening->leaf_values[j], buffer + offset, 16);
            offset += 16;
        }
        
        // Read path length
        if (offset + 4 > buffer_size) {
            // Clean up on error
            for (size_t j = 0; j <= i; j++) {
                if (proof->openings[j]) {
                    free(proof->openings[j]->auth_path);
                    free(proof->openings[j]);
                }
            }
            free(proof->openings);
            proof->openings = NULL;
            proof->num_openings = 0;
            return -1;
        }
        memcpy(&opening->path_len, buffer + offset, 4);
        offset += 4;
        
        // Sanity check path length
        if (opening->path_len > 10000) {  // Reasonable upper limit
            // Clean up on error
            for (size_t j = 0; j <= i; j++) {
                if (proof->openings[j]) {
                    free(proof->openings[j]->auth_path);
                    free(proof->openings[j]);
                }
            }
            free(proof->openings);
            proof->openings = NULL;
            proof->num_openings = 0;
            return -1;
        }
        
        // Allocate and read authentication path
        if (opening->path_len > 0) {
            opening->auth_path = malloc(opening->path_len);
            if (!opening->auth_path) {
                // Clean up on error
                for (size_t j = 0; j <= i; j++) {
                    if (proof->openings[j]) {
                        if (j < i) {
                            free(proof->openings[j]->auth_path);
                        }
                        free(proof->openings[j]);
                    }
                }
                free(proof->openings);
                proof->openings = NULL;
                proof->num_openings = 0;
                return -1;
            }
        } else {
            opening->auth_path = NULL;
        }
        
        if (opening->path_len > 0) {
            if (offset + opening->path_len > buffer_size) {
                // Clean up on error
                for (size_t j = 0; j <= i; j++) {
                    if (proof->openings[j]) {
                        free(proof->openings[j]->auth_path);
                        free(proof->openings[j]);
                    }
                }
                free(proof->openings);
                proof->openings = NULL;
                proof->num_openings = 0;
                return -1;
            }
            memcpy(opening->auth_path, buffer + offset, opening->path_len);
            offset += opening->path_len;
        }
    }
    
    return offset;
}

void merkle_commitment_proof_free(merkle_commitment_proof_t* proof)
{
    if (!proof) {
        return;
    }
    
    if (proof->openings) {
        for (size_t i = 0; i < proof->num_openings; i++) {
            if (proof->openings[i]) {
                free(proof->openings[i]->auth_path);
                free(proof->openings[i]);
            }
        }
        free(proof->openings);
    }
}

uint32_t merkle_point_to_leaf_index(
    const gf128_t* eval_point,
    size_t num_vars)
{
    // Convert binary evaluation point to index
    // For multilinear polynomials over {0,1}^n, we interpret
    // the point as a binary number
    
    uint32_t index = 0;
    for (size_t i = 0; i < num_vars; i++) {
        // Check if variable i is 1
        if (!gf128_eq(eval_point[i], gf128_zero())) {
            index |= (1U << i);
        }
    }
    
    return index;
}

void merkle_free_commitment_proof(merkle_commitment_proof_t* proof) {
    if (!proof) return;
    
    if (proof->openings) {
        for (size_t i = 0; i < proof->num_openings; i++) {
            if (proof->openings[i]) {
                if (proof->openings[i]->auth_path) {
                    free(proof->openings[i]->auth_path);
                }
                free(proof->openings[i]);
            }
        }
        free(proof->openings);
    }
    
    free(proof);
}