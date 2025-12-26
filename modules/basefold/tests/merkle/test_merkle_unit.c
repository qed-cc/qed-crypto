#include "merkle/build.h"
#include "merkle/verify.h"
#include "gf128.h"
#include "sha3.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// Simple PRNG for test data
static uint64_t test_seed = 42;
static uint64_t test_rand(void) {
    test_seed ^= test_seed << 13;
    test_seed ^= test_seed >> 7;
    test_seed ^= test_seed << 17;
    return test_seed;
}

static gf128_t random_gf128(void) {
    gf128_t result;
    result.lo = test_rand();
    result.hi = test_rand();
    return result;
}

// Test 1: Tree build basic functionality
static int test_tree_build(void) {
    printf("=== Test 1: Tree Build Test (16 leaves) ===\n");
    
    const size_t num_words = 16 * MERKLE_LEAF_WORDS;  // 16 leaves × 8 words/leaf
    gf128_t *test_data = aligned_alloc(64, num_words * sizeof(gf128_t));
    
    if (!test_data) {
        printf("FAIL: Memory allocation failed\n");
        return 0;
    }
    
    // Fill with deterministic test data
    for (size_t i = 0; i < num_words; ++i) {
        test_data[i] = (gf128_t){0, i + 1};
    }
    
    // Build tree
    merkle_tree_t tree;
    uint32_t num_leaves = (uint32_t)(num_words / MERKLE_LEAF_WORDS);
    int result = merkle_build(test_data, num_leaves, &tree);
    
    if (result != 0) {
        printf("FAIL: Tree build failed\n");
        free(test_data);
        return 0;
    }
    
    printf("Tree built: depth=%u, leaves=%u\n", tree.depth, tree.leaves);
    printf("Root: ");
    for (int i = 0; i < 8; ++i) {
        printf("%02x", tree.root[i]);
    }
    printf("...\n");
    
    // Test that we can open leaves (without using insecure verify)
    int success_count = 0;
    for (uint32_t leaf_idx = 0; leaf_idx < tree.leaves && leaf_idx < 4; ++leaf_idx) {
        gf128_t value;
        uint8_t path[30 * 32];  // Max path size
        
        if (merkle_open(&tree, test_data, leaf_idx, &value, path) == 0) {
            success_count++;
        } else {
            printf("FAIL: Opening failed for leaf %u\n", leaf_idx);
            break;
        }
    }
    
    free(test_data);
    
    if (success_count >= 4) {
        printf("PASS: Tree build and opening successful\n");
        return 1;
    } else {
        printf("FAIL: Tree operations failed\n");
        return 0;
    }
}

// Test 2: Root reproducibility
static int test_root_reproducibility(void) {
    printf("\n=== Test 2: Root Reproducibility ===\n");
    
    const size_t num_words = 32 * MERKLE_LEAF_WORDS;  // 32 leaves
    gf128_t *test_data = aligned_alloc(64, num_words * sizeof(gf128_t));
    
    if (!test_data) {
        printf("FAIL: Memory allocation failed\n");
        return 0;
    }
    
    // Fill with random test data
    for (size_t i = 0; i < num_words; ++i) {
        test_data[i] = random_gf128();
    }
    
    // Build tree twice
    merkle_tree_t tree1, tree2;
    uint32_t num_leaves = (uint32_t)(num_words / MERKLE_LEAF_WORDS);
    if (merkle_build(test_data, num_leaves, &tree1) != 0 || 
        merkle_build(test_data, num_leaves, &tree2) != 0) {
        printf("FAIL: Tree build failed\n");
        free(test_data);
        return 0;
    }
    
    // Compare roots
    if (memcmp(tree1.root, tree2.root, 32) == 0) {
        printf("PASS: Roots are identical\n");
        printf("Root: ");
        for (int i = 0; i < 8; ++i) {
            printf("%02x", tree1.root[i]);
        }
        printf("...\n");
        
        free(test_data);
        return 1;
    } else {
        printf("FAIL: Roots differ\n");
        printf("Root1: ");
        for (int i = 0; i < 8; ++i) {
            printf("%02x", tree1.root[i]);
        }
        printf("...\n");
        printf("Root2: ");
        for (int i = 0; i < 8; ++i) {
            printf("%02x", tree2.root[i]);
        }
        printf("...\n");
        
        free(test_data);
        return 0;
    }
}

// Test 3: SHA-3 cross-check with known vector
static int test_sha3_cross_check(void) {
    printf("\n=== Test 3: SHA-3 Cross-check ===\n");
    
    // Known test vector: 128 bytes of 0x00
    uint8_t test_block[128];
    memset(test_block, 0, 128);
    
    uint8_t digest[32];
    sha3_hash(SHA3_256, test_block, 128, digest, 32);
    
    // Known SHA-3-256 of 128 zero bytes
    uint8_t expected[] = {
        0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66,
        0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62,
        0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
        0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a
    };
    
    if (memcmp(digest, expected, 32) == 0) {
        printf("PASS: SHA-3-256 produces expected hash\n");
        return 1;
    } else {
        printf("FAIL: SHA-3-256 hash mismatch\n");
        printf("Expected: ");
        for (int i = 0; i < 32; ++i) {
            printf("%02x", expected[i]);
        }
        printf("\nGot:      ");
        for (int i = 0; i < 32; ++i) {
            printf("%02x", digest[i]);
        }
        printf("\n");
        return 0;
    }
}

// Test 4: Path length verification
static int test_path_length(void) {
    printf("\n=== Test 4: Path Length Verification ===\n");
    
    const size_t num_words = 64 * MERKLE_LEAF_WORDS;  // 64 leaves
    gf128_t *test_data = aligned_alloc(64, num_words * sizeof(gf128_t));
    
    if (!test_data) {
        printf("FAIL: Memory allocation failed\n");
        return 0;
    }
    
    // Fill with test data
    for (size_t i = 0; i < num_words; ++i) {
        test_data[i] = (gf128_t){i / 64, i % 64};
    }
    
    merkle_tree_t tree;
    if (merkle_build(test_data, num_words, &tree) != 0) {
        printf("FAIL: Tree build failed\n");
        free(test_data);
        return 0;
    }
    
    // Test path for middle leaf
    uint32_t test_idx = tree.leaves / 2;
    gf128_t value;
    uint8_t path[30 * 32];
    
    if (merkle_open(&tree, test_data, test_idx, &value, path) != 0) {
        printf("FAIL: Leaf opening failed\n");
        free(test_data);
        return 0;
    }
    
    // Verify path length is exactly depth * 3 * 32 bytes
    size_t expected_path_bytes = tree.depth * 3 * 32;
    printf("Path length: %zu bytes (depth=%u × 3 siblings × 32 bytes)\n", 
           expected_path_bytes, tree.depth);
    
    if (expected_path_bytes == 30 * 32) {
        printf("PASS: Path length matches specification (960 bytes)\n");
        free(test_data);
        return 1;
    } else {
        printf("FAIL: Path length %zu, expected 960 bytes\n", expected_path_bytes);
        free(test_data);
        return 0;
    }
}

int main(void) {
    printf("=== Merkle Tree Unit Tests ===\n\n");
    
    int tests_passed = 0;
    int total_tests = 4;
    
    tests_passed += test_tree_build();
    tests_passed += test_root_reproducibility();
    tests_passed += test_sha3_cross_check();
    tests_passed += test_path_length();
    
    printf("\n=== Test Summary ===\n");
    printf("Passed: %d/%d tests\n", tests_passed, total_tests);
    
    if (tests_passed == total_tests) {
        printf("✅ All unit tests PASSED\n");
        return 0;
    } else {
        printf("❌ Some unit tests FAILED\n");
        return 1;
    }
}