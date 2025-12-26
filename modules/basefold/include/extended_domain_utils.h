#ifndef BASEFOLD_EXTENDED_DOMAIN_UTILS_H
#define BASEFOLD_EXTENDED_DOMAIN_UTILS_H

#include <stddef.h>
#include <stdint.h>
#include <gf128.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Map evaluation point in original domain to extended domain index
 * 
 * When using extended domain for zero-knowledge, we need to map evaluation
 * points from the original {0,1}^n domain to indices in the extended
 * {0,1}^(n+2) domain.
 * 
 * The mapping preserves the original values in the first quadrant:
 * - Points in {0,1}^n map to indices [0, 2^n) in extended domain
 * - Extended domain has size 2^(n+2) = 4 * 2^n
 * 
 * @param eval_point Evaluation point in {0,1}^n
 * @param num_vars Number of variables in original domain (n)
 * @param use_extended Whether to use extended domain mapping
 * @return Leaf index in the (possibly extended) Merkle tree
 */
uint32_t merkle_point_to_extended_leaf_index(
    const gf128_t* eval_point,
    size_t num_vars,
    bool use_extended
);

/**
 * @brief Convert gate index to extended domain leaf index
 * 
 * In the extended domain, each gate's 4 field elements (L,R,O,S) map to
 * a specific leaf in the Merkle tree. This function handles the conversion.
 * 
 * @param gate_index Index of the gate in the original trace
 * @param use_extended Whether extended domain is in use
 * @return Leaf index in the Merkle tree
 */
static inline uint32_t gate_to_extended_leaf_index(
    uint32_t gate_index,
    bool use_extended
) {
    // In our layout, leaves group 8 field elements
    // Each gate contributes 4 field elements (L,R,O,S)
    // So 2 gates per leaf
    return gate_index / 2;
}

/**
 * @brief Check if evaluation point is in the original (unmasked) quadrant
 * 
 * In the extended domain {0,1}^(n+2), the first quadrant (where the
 * extension variables are both 0) contains the original unmasked values.
 * 
 * @param eval_point Evaluation point in extended domain
 * @param num_vars Number of original variables (n)
 * @return true if point is in original quadrant
 */
static inline bool is_original_quadrant_point(
    const gf128_t* eval_point,
    size_t num_vars
) {
    // Check if extension variables (at positions n and n+1) are both 0
    return gf128_eq(eval_point[num_vars], gf128_zero()) &&
           gf128_eq(eval_point[num_vars + 1], gf128_zero());
}

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_EXTENDED_DOMAIN_UTILS_H */