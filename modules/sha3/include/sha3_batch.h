/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef SHA3_BATCH_H
#define SHA3_BATCH_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Compute 4 SHA3-256 hashes in parallel using AVX2
 * 
 * @param in Array of 4 input buffers
 * @param inlen Array of 4 input lengths
 * @param out Output array for 4 32-byte hashes
 */
void sha3_256_x4_avx2(const uint8_t *in[4], size_t inlen[4], uint8_t out[4][32]);

/**
 * @brief Verify 4 Merkle paths in parallel using batch SHA3
 * 
 * @param paths 4 Merkle paths, each with 10 levels, 64 bytes per node
 * @param leaves 4 leaf values (32 bytes each)
 * @param root Expected root hash (32 bytes)
 * @param directions Direction bits for each path (0=left, 1=right)
 * @param results Output array of verification results
 * @return Number of successful verifications
 */
int verify_merkle_batch_x4_avx2(
    const uint8_t paths[4][10][64],
    const uint8_t leaves[4][32],
    const uint8_t root[32],
    int directions[4][10],
    bool results[4]
);

#ifdef __cplusplus
}
#endif

#endif /* SHA3_BATCH_H */