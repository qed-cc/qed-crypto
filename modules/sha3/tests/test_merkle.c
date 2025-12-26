/* SPDX-License-Identifier: Apache-2.0 */
/* Test suite for 4-ary Merkle tree (`sha3_merkle_tree4_32`) */
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "sha3.h"

// Helper to compute SHA3-256 on a padded branch of up to 4 leaves
static void expected_root(const uint8_t *leaves, size_t n, uint8_t *out) {
    size_t D = SHA3_256_DIGEST_SIZE;
    size_t R = sha3_get_block_size(SHA3_256);
    uint8_t buf[136];
    // pack up to 4 leaves (duplicate last if fewer)
    for (size_t j = 0; j < 4; j++) {
        size_t idx = j < n ? j : (n - 1);
        memcpy(buf + j * D, leaves + idx * D, D);
    }
    // padding
    buf[4 * D] = 0x06;
    memset(buf + 4 * D + 1, 0, R - (4 * D + 1));
    buf[R - 1] ^= 0x80;
    // hash
    sha3_hash(SHA3_256, buf, R, out, D);
}

int main(void) {
    // Test N = 1
    uint8_t leaf1[SHA3_256_DIGEST_SIZE] = {0};
    uint8_t root1[SHA3_256_DIGEST_SIZE];
    uint8_t exp1[SHA3_256_DIGEST_SIZE];
    assert(sha3_merkle_tree4_32(leaf1, 1, root1) == 0);
    expected_root(leaf1, 1, exp1);
    assert(memcmp(root1, exp1, SHA3_256_DIGEST_SIZE) == 0);
    // Test N = 2
    uint8_t leaves2[2 * SHA3_256_DIGEST_SIZE];
    for (size_t i = 0; i < SHA3_256_DIGEST_SIZE; i++) leaves2[i] = (uint8_t)i;
    for (size_t i = 0; i < SHA3_256_DIGEST_SIZE; i++) leaves2[SHA3_256_DIGEST_SIZE + i] = (uint8_t)(i ^ 0xFF);
    uint8_t root2[SHA3_256_DIGEST_SIZE], exp2[SHA3_256_DIGEST_SIZE];
    assert(sha3_merkle_tree4_32(leaves2, 2, root2) == 0);
    expected_root(leaves2, 2, exp2);
    assert(memcmp(root2, exp2, SHA3_256_DIGEST_SIZE) == 0);
    // Test N = 4 (exact branch)
    uint8_t leaves4[4 * SHA3_256_DIGEST_SIZE];
    for (size_t i = 0; i < 4 * SHA3_256_DIGEST_SIZE; i++) leaves4[i] = (uint8_t)(i & 0xFF);
    uint8_t root4[SHA3_256_DIGEST_SIZE], exp4[SHA3_256_DIGEST_SIZE];
    assert(sha3_merkle_tree4_32(leaves4, 4, root4) == 0);
    expected_root(leaves4, 4, exp4);
    assert(memcmp(root4, exp4, SHA3_256_DIGEST_SIZE) == 0);
    printf("test_merkle: all tests passed\n");
    return 0;
}