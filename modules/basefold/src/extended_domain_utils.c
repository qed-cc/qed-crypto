#include "extended_domain_utils.h"

uint32_t merkle_point_to_extended_leaf_index(
    const gf128_t* eval_point,
    size_t num_vars,
    bool use_extended)
{
    if (!use_extended) {
        // Original domain: convert {0,1}^n point to index
        uint32_t index = 0;
        for (size_t i = 0; i < num_vars; i++) {
            // Check if variable i is 1
            if (!gf128_eq(eval_point[i], gf128_zero())) {
                index |= (1U << i);
            }
        }
        // In original domain, gate index maps directly to leaf index
        // Each leaf contains 8 field elements (2 gates)
        return index / 2;
    }
    
    // Extended domain: convert {0,1}^(n+2) point to index
    // The evaluation point should have n+2 coordinates
    uint32_t index = 0;
    
    // First n bits from original variables
    for (size_t i = 0; i < num_vars; i++) {
        if (!gf128_eq(eval_point[i], gf128_zero())) {
            index |= (1U << i);
        }
    }
    
    // Next 2 bits from extension variables
    // These determine which quadrant we're in
    if (!gf128_eq(eval_point[num_vars], gf128_zero())) {
        index |= (1U << num_vars);
    }
    if (!gf128_eq(eval_point[num_vars + 1], gf128_zero())) {
        index |= (1U << (num_vars + 1));
    }
    
    // In extended domain, we have 4x as many field elements
    // But still 8 field elements per leaf (2 gates worth)
    return index / 2;
}