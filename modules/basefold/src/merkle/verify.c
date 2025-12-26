#include "merkle/verify.h"
#include "../../sha3/include/sha3.h"
#include <string.h>

int merkle_verify_leaf_group(const uint8_t root[32],
                  uint32_t depth,
                  uint32_t idx,
                  const gf128_t *leaf_values,  // Array of 8 GF128 values
                  const uint8_t *path) {
    if (!root || !leaf_values || !path) {
        return -1;
    }
    
    // Start by hashing the leaf group
    uint8_t current_hash[32];
    // SECURITY FIX: Add domain separation to match build.c
    uint8_t leaf_data[129];  // 1 byte separator + 128 bytes data
    
    // SECURITY: Domain separator for leaf nodes (must match build.c)
    leaf_data[0] = 0x00;  // Leaf domain
    
    // Hash the 8 GF128 values that form this leaf
    for (int i = 0; i < 8; ++i) {
        uint8_t *out = leaf_data + 1 + i * 16;  // Offset by 1 for domain separator
        gf128_t a = leaf_values[i];
        
        // Inline gf128_to_le for consistency with build.c
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
    
    sha3_hash(SHA3_256, leaf_data, 129, current_hash, 32);
    
    // Walk up the tree, level by level
    uint32_t current_idx = idx;
    const uint8_t *path_ptr = path;
    
    for (uint32_t level = 0; level < depth; ++level) {
        uint32_t position = current_idx & 3U;  // Position within group (0-3)
        
        // Reconstruct parent node from 4 children
        // SECURITY FIX: Add domain separation to match build.c
        uint8_t node_data[129];  // 1 byte separator + 128 bytes child digests
        uint8_t children[4 * 32];
        memset(children, 0, sizeof(children));
        
        // Insert the 3 siblings from the path
        int sibling_idx = 0;
        for (int i = 0; i < 4; ++i) {
            if (i == position) {
                // This is our child - use current_hash
                memcpy(children + i * 32, current_hash, 32);
            } else {
                // This is a sibling - get from path
                memcpy(children + i * 32, path_ptr + sibling_idx * 32, 32);
                sibling_idx++;
            }
        }
        
        // SECURITY: Domain separator for internal nodes (must match build.c)
        node_data[0] = 0x01;  // Internal node domain
        memcpy(node_data + 1, children, 4 * 32);
        
        // Hash the parent node with domain separation
        sha3_hash(SHA3_256, node_data, 129, current_hash, 32);
        
        // Move to next level
        path_ptr += 3 * 32;  // Skip 3 sibling digests
        current_idx >>= 2;   // Move to parent index
    }
    
    // Compare computed root with expected root
    return memcmp(current_hash, root, 32) == 0 ? 0 : -1;
}


