/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_commitments.h"
#include "../../sha3/include/sha3.h"
#include "../../cmptr_trees/include/cmptr_trees.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Commitment scheme structure
struct cmptr_commitment_scheme {
    cmptr_commit_config_t config;
    cmptr_tree_t* merkle_tree;  // For Merkle-based commitments
    
    // Statistics
    uint64_t total_openings;
    uint64_t total_updates;
    double total_verify_time_ms;
};

// Commitment structure
struct cmptr_commitment {
    cmptr_commitment_scheme_t* scheme;
    uint8_t value[CMPTR_COMMIT_SIZE];
    
    // Store values for opening (simplified)
    uint8_t** values;
    size_t* value_sizes;
    size_t vector_size;
};

// Proof structure
struct cmptr_commit_proof {
    cmptr_tree_proof_t* merkle_proof;  // For Merkle type
    uint8_t* raw_proof;                 // For other types
    size_t proof_size;
    size_t index;
};

// Batch structure
struct cmptr_commit_batch {
    cmptr_commitment_scheme_t* scheme;
    size_t capacity;
    size_t count;
};

// Initialize scheme
cmptr_commitment_scheme_t* cmptr_commit_scheme_new(const cmptr_commit_config_t* config) {
    cmptr_commitment_scheme_t* scheme = calloc(1, sizeof(cmptr_commitment_scheme_t));
    if (!scheme) return NULL;
    
    if (config) {
        scheme->config = *config;
    } else {
        // Default config
        scheme->config.type = CMPTR_COMMIT_MERKLE;
        scheme->config.enable_updates = false;
        scheme->config.enable_aggregation = false;
    }
    
    // For Merkle type, create underlying tree
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        cmptr_tree_config_t tree_config = {
            .type = CMPTR_TREE_STANDARD,
            .optimization_flags = CMPTR_TREE_OPT_BATCH,
            .leaf_count_hint = scheme->config.vector_size_hint,
            .cache_enabled = true
        };
        
        scheme->merkle_tree = cmptr_tree_new(&tree_config);
        if (!scheme->merkle_tree) {
            free(scheme);
            return NULL;
        }
    }
    
    return scheme;
}

// Commit to vector
cmptr_commitment_t* cmptr_commit_vector(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t** values,
    const size_t* value_sizes,
    size_t count
) {
    if (!scheme || !values || !value_sizes || count == 0) return NULL;
    
    cmptr_commitment_t* commitment = calloc(1, sizeof(cmptr_commitment_t));
    if (!commitment) return NULL;
    
    commitment->scheme = scheme;
    commitment->vector_size = count;
    
    // Store values (for opening later)
    commitment->values = calloc(count, sizeof(uint8_t*));
    commitment->value_sizes = calloc(count, sizeof(size_t));
    
    if (!commitment->values || !commitment->value_sizes) {
        cmptr_commit_free(commitment);
        return NULL;
    }
    
    // Copy values and add to tree
    for (size_t i = 0; i < count; i++) {
        commitment->values[i] = malloc(value_sizes[i]);
        if (!commitment->values[i]) {
            cmptr_commit_free(commitment);
            return NULL;
        }
        
        memcpy(commitment->values[i], values[i], value_sizes[i]);
        commitment->value_sizes[i] = value_sizes[i];
        
        // Add to Merkle tree
        if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
            cmptr_tree_add(scheme->merkle_tree, values[i], value_sizes[i]);
        }
    }
    
    // Get commitment value
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        cmptr_tree_root(scheme->merkle_tree, commitment->value);
    } else {
        // For other types, simulate with hash of all values
        sha3_ctx ctx;
        sha3_init(&ctx, SHA3_256);
        sha3_update(&ctx, (const uint8_t*)"vector_commit", 13);
        
        for (size_t i = 0; i < count; i++) {
            sha3_update(&ctx, values[i], value_sizes[i]);
        }
        
        sha3_final(&ctx, commitment->value, 32);
    }
    
    return commitment;
}

// Open commitment
cmptr_commit_proof_t* cmptr_commit_open(
    cmptr_commitment_scheme_t* scheme,
    const cmptr_commitment_t* commitment,
    size_t index
) {
    if (!scheme || !commitment || index >= commitment->vector_size) return NULL;
    
    cmptr_commit_proof_t* proof = calloc(1, sizeof(cmptr_commit_proof_t));
    if (!proof) return NULL;
    
    proof->index = index;
    scheme->total_openings++;
    
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        proof->merkle_proof = cmptr_tree_prove(scheme->merkle_tree, index);
        if (!proof->merkle_proof) {
            free(proof);
            return NULL;
        }
    } else {
        // For other types, create simulated proof
        proof->raw_proof = calloc(1, 1024);  // Dummy proof
        if (!proof->raw_proof) {
            free(proof);
            return NULL;
        }
        
        // Simulate proof generation
        sha3_ctx ctx;
        sha3_init(&ctx, SHA3_256);
        sha3_update(&ctx, (const uint8_t*)"proof", 5);
        sha3_update(&ctx, commitment->value, CMPTR_COMMIT_SIZE);
        sha3_update(&ctx, (const uint8_t*)&index, sizeof(index));
        sha3_final(&ctx, proof->raw_proof, 32);
        
        proof->proof_size = 256;  // Simulated size
    }
    
    return proof;
}

// Verify opening
bool cmptr_commit_verify(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t commitment[CMPTR_COMMIT_SIZE],
    size_t index,
    const uint8_t* value,
    size_t value_size,
    const cmptr_commit_proof_t* proof
) {
    if (!scheme || !commitment || !value || !proof) return false;
    
    clock_t start = clock();
    bool result = false;
    
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        result = cmptr_tree_verify(
            commitment, index,
            value, value_size,
            proof->merkle_proof
        );
    } else {
        // Simulate verification
        result = proof->proof_size > 0 && proof->index == index;
    }
    
    clock_t end = clock();
    double ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    scheme->total_verify_time_ms += ms;
    
    return result;
}

// Get commitment value
bool cmptr_commit_get_value(
    const cmptr_commitment_t* commitment,
    uint8_t commitment_out[CMPTR_COMMIT_SIZE]
) {
    if (!commitment || !commitment_out) return false;
    memcpy(commitment_out, commitment->value, CMPTR_COMMIT_SIZE);
    return true;
}

// Batch operations
cmptr_commit_batch_t* cmptr_commit_batch_new(cmptr_commitment_scheme_t* scheme) {
    if (!scheme) return NULL;
    
    cmptr_commit_batch_t* batch = calloc(1, sizeof(cmptr_commit_batch_t));
    if (!batch) return NULL;
    
    batch->scheme = scheme;
    batch->capacity = 1024;
    
    return batch;
}

// Batch open
bool cmptr_commit_batch_open(
    cmptr_commit_batch_t* batch,
    const cmptr_commitment_t* commitment,
    const size_t* indices,
    size_t count,
    cmptr_commit_proof_t** proofs_out
) {
    if (!batch || !commitment || !indices || !proofs_out || count == 0) return false;
    
    // Generate individual proofs (could be optimized)
    for (size_t i = 0; i < count; i++) {
        proofs_out[i] = cmptr_commit_open(batch->scheme, commitment, indices[i]);
        if (!proofs_out[i]) {
            // Cleanup on failure
            for (size_t j = 0; j < i; j++) {
                cmptr_commit_proof_free(proofs_out[j]);
            }
            return false;
        }
    }
    
    return true;
}

// Batch verify
bool cmptr_commit_batch_verify(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t commitment[CMPTR_COMMIT_SIZE],
    const size_t* indices,
    const uint8_t** values,
    const size_t* value_sizes,
    const cmptr_commit_proof_t** proofs,
    size_t count
) {
    if (!scheme || !commitment || count == 0) return false;
    
    // Verify each individually (could be optimized with batch verification)
    for (size_t i = 0; i < count; i++) {
        if (!cmptr_commit_verify(scheme, commitment, indices[i],
                                values[i], value_sizes[i], proofs[i])) {
            return false;
        }
    }
    
    return true;
}

void cmptr_commit_batch_free(cmptr_commit_batch_t* batch) {
    if (!batch) return;
    free(batch);
}

// Update commitment
bool cmptr_commit_update(
    cmptr_commitment_scheme_t* scheme,
    cmptr_commitment_t* commitment,
    size_t index,
    const uint8_t* new_value,
    size_t new_value_size
) {
    if (!scheme || !commitment || !new_value || index >= commitment->vector_size) {
        return false;
    }
    
    if (!scheme->config.enable_updates) {
        return false;  // Updates not enabled
    }
    
    // Update stored value
    free(commitment->values[index]);
    commitment->values[index] = malloc(new_value_size);
    if (!commitment->values[index]) return false;
    
    memcpy(commitment->values[index], new_value, new_value_size);
    commitment->value_sizes[index] = new_value_size;
    
    // Update tree and recompute root
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        cmptr_tree_update(scheme->merkle_tree, index, new_value, new_value_size);
        cmptr_tree_root(scheme->merkle_tree, commitment->value);
    }
    
    scheme->total_updates++;
    return true;
}

// Get statistics
void cmptr_commit_get_stats(
    const cmptr_commitment_scheme_t* scheme,
    cmptr_commit_stats_t* stats_out
) {
    if (!scheme || !stats_out) return;
    
    stats_out->total_openings = scheme->total_openings;
    stats_out->total_updates = scheme->total_updates;
    
    if (scheme->total_openings > 0) {
        stats_out->verification_time_avg_ms = 
            scheme->total_verify_time_ms / scheme->total_openings;
    } else {
        stats_out->verification_time_avg_ms = 0.0;
    }
    
    // Estimate sizes based on type
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        stats_out->commitment_size = CMPTR_COMMIT_SIZE;
        stats_out->proof_size_avg = 32 * 20;  // ~20 siblings for 1M leaves
    } else {
        stats_out->commitment_size = CMPTR_COMMIT_SIZE;
        stats_out->proof_size_avg = 1024;  // Simulated
    }
}

// Free resources
void cmptr_commit_scheme_free(cmptr_commitment_scheme_t* scheme) {
    if (!scheme) return;
    
    if (scheme->merkle_tree) {
        cmptr_tree_free(scheme->merkle_tree);
    }
    
    free(scheme);
}

void cmptr_commit_free(cmptr_commitment_t* commitment) {
    if (!commitment) return;
    
    // Free stored values
    if (commitment->values) {
        for (size_t i = 0; i < commitment->vector_size; i++) {
            free(commitment->values[i]);
        }
        free(commitment->values);
    }
    
    free(commitment->value_sizes);
    free(commitment);
}

void cmptr_commit_proof_free(cmptr_commit_proof_t* proof) {
    if (!proof) return;
    
    if (proof->merkle_proof) {
        cmptr_tree_proof_free(proof->merkle_proof);
    }
    
    free(proof->raw_proof);
    free(proof);
}

// Utility: Commit to single value
bool cmptr_commit_single(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t* value,
    size_t value_size,
    uint8_t commitment_out[CMPTR_COMMIT_SIZE]
) {
    if (!scheme || !value || !commitment_out) return false;
    
    const uint8_t* values[] = {value};
    size_t sizes[] = {value_size};
    
    cmptr_commitment_t* commitment = cmptr_commit_vector(scheme, values, sizes, 1);
    if (!commitment) return false;
    
    memcpy(commitment_out, commitment->value, CMPTR_COMMIT_SIZE);
    cmptr_commit_free(commitment);
    
    return true;
}

// Proof size estimate
size_t cmptr_commit_proof_size_estimate(
    const cmptr_commitment_scheme_t* scheme,
    size_t vector_size,
    size_t indices_count
) {
    if (!scheme) return 0;
    
    // Estimate based on type
    if (scheme->config.type == CMPTR_COMMIT_MERKLE) {
        // Log2(vector_size) * 32 bytes per index
        size_t height = 0;
        size_t n = vector_size;
        while (n > 1) {
            height++;
            n /= 2;
        }
        return height * 32 * indices_count;
    }
    
    // Other types: constant size
    return 1024 * indices_count;
}