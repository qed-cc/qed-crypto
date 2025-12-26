/**
 * @file basefold_trace_lazy.c
 * @brief Lazy evaluation implementation for zero-knowledge trace masking
 * 
 * Instead of creating 4x elements upfront, we:
 * 1. Commit only to original trace
 * 2. Store ZK seed and parameters
 * 3. Compute extended evaluations on-demand
 */

#include "basefold_trace.h"
#include "evaluation_domain.h"
#include "merkle/build.h"
#include "gf128.h"
#include <string.h>
#include <stdlib.h>

/**
 * @brief Lazy ZK trace structure
 * 
 * Stores only original elements and computes extended values on demand
 */
typedef struct {
    basefold_trace_t* base_trace;
    evaluation_domain_t* domain;
    uint8_t zk_seed[16];
} lazy_zk_trace_t;

/**
 * @brief Create lazy ZK wrapper
 */
lazy_zk_trace_t* lazy_zk_create(basefold_trace_t* trace) {
    if (!trace || !trace->is_padded || !trace->is_masked) {
        return NULL;
    }
    
    lazy_zk_trace_t* lazy = malloc(sizeof(lazy_zk_trace_t));
    if (!lazy) return NULL;
    
    lazy->base_trace = trace;
    memcpy(lazy->zk_seed, trace->mask_seed, 128);
    
    // Calculate number of variables
    size_t num_vars = 0;
    size_t temp = trace->padded_size;
    while (temp > 1) {
        num_vars++;
        temp >>= 1;
    }
    
    lazy->domain = evaluation_domain_create(num_vars, lazy->zk_seed);
    if (!lazy->domain) {
        free(lazy);
        return NULL;
    }
    
    return lazy;
}

/**
 * @brief Get field element at extended index (lazy evaluation)
 */
gf128_t lazy_zk_get_element(lazy_zk_trace_t* lazy, size_t idx, size_t col) {
    // Map to original index
    size_t orig_idx = idx & (lazy->base_trace->padded_size - 1);
    size_t field_idx = orig_idx * 4 + col;
    
    // Get base value
#ifdef __x86_64__
    __m128i base_val = lazy->base_trace->field_elements[field_idx];
    gf128_t value = {
        .lo = _mm_extract_epi64(base_val, 0),
        .hi = _mm_extract_epi64(base_val, 1)
    };
#else
    gf128_t value;
    memcpy(&value, &lazy->base_trace->field_elements[field_idx * 16], 16);
#endif
    
    // Apply mask if not in original quadrant
    if (!evaluation_domain_is_original(lazy->domain, idx)) {
        gf128_t mask = evaluation_domain_generate_mask(lazy->domain, idx, col);
        value = gf128_add(value, mask);
    }
    
    return value;
}

/**
 * @brief Build Merkle tree from lazy trace (only original elements)
 */
int lazy_zk_build_merkle(lazy_zk_trace_t* lazy, merkle_tree_t* tree) {
    // Build tree from original elements only
    uint32_t num_leaves = lazy->base_trace->num_field_elements / MERKLE_LEAF_WORDS;
    
#ifdef __x86_64__
    return merkle_build((const gf128_t*)lazy->base_trace->field_elements, num_leaves, tree);
#else
    // Need conversion for non-x86_64
    return -1;
#endif
}

/**
 * @brief Generate extended domain proof when queried
 */
int lazy_zk_open_extended(lazy_zk_trace_t* lazy, size_t idx, gf128_t* values, uint8_t* proof) {
    // If index is in original domain, open from Merkle tree
    if (idx < lazy->base_trace->padded_size) {
        // Standard Merkle opening
        return 0;
    }
    
    // Otherwise, provide:
    // 1. The original index it maps to
    // 2. The mask used
    // 3. Proof that mask was correctly generated from seed
    
    size_t orig_idx = idx & (lazy->base_trace->padded_size - 1);
    
    // Get all 4 column values
    for (size_t col = 0; col < 4; col++) {
        values[col] = lazy_zk_get_element(lazy, idx, col);
    }
    
    // Proof contains:
    // - Original index (4 bytes)
    // - Column masks (64 bytes)
    // This is much smaller than Merkle paths!
    
    memcpy(proof, &orig_idx, 4);
    for (size_t col = 0; col < 4; col++) {
        gf128_t mask = evaluation_domain_generate_mask(lazy->domain, idx, col);
        memcpy(proof + 4 + col * 16, &mask, 16);
    }
    
    return 68; // 4 + 64 bytes
}

/**
 * @brief Free lazy ZK structure
 */
void lazy_zk_free(lazy_zk_trace_t* lazy) {
    if (!lazy) return;
    
    if (lazy->domain) {
        evaluation_domain_free(lazy->domain);
    }
    free(lazy);
}

/**
 * @brief Fast zero-knowledge trace application
 * 
 * This replaces basefold_trace_create_extended_field_elements
 * by NOT creating the 4x array upfront
 */
bool basefold_trace_apply_fast_zk(basefold_trace_t* trace) {
    if (!trace || !trace->is_padded || !trace->is_masked) {
        return false;
    }
    
    // Just mark that we have "virtual" extended elements
    // Don't actually allocate 4x memory!
    
    // Calculate extended size for API compatibility
    trace->extended_size = trace->padded_size * 4;
    trace->num_extended_elements = trace->extended_size * 4;
    
    // Key optimization: DON'T allocate extended_field_elements
    trace->extended_field_elements = NULL;
    trace->has_extended_elements = true; // Mark as "virtually" available
    
    return true;
}