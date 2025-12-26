#ifndef MERKLE_VERIFY_H
#define MERKLE_VERIFY_H

#include <stdint.h>
#include "gf128.h"

#ifdef __cplusplus
extern "C" {
#endif


/**
 * @brief Verify Merkle path for a complete leaf group
 * 
 * @param root Expected root digest (32 bytes)
 * @param depth Tree depth
 * @param idx Leaf index being verified
 * @param leaf_values Array of 8 GF128 values forming the complete leaf
 * @param path Authentication path
 * @return 0 on success, -1 on failure
 * 
 * This is the secure version that verifies the actual leaf content
 * by hashing all 8 GF128 values that form the leaf.
 */
int merkle_verify_leaf_group(const uint8_t root[32],
                  uint32_t depth,
                  uint32_t idx,
                  const gf128_t *leaf_values,
                  const uint8_t *path);


#ifdef __cplusplus
}
#endif

#endif // MERKLE_VERIFY_H