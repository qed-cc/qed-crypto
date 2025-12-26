#include "merkle/build.h"
#include "merkle/verify.h"
#include "gf128.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Big-scale smoke test for CI (≤5s target)
// Tests with production-scale tree but limited operations

static uint64_t test_seed = 123456789;
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

int main(void) {
    printf("=== Merkle Tree Big-Scale Smoke Test ===\n");
    printf("Target: Complete test in ≤5 seconds\n\n");
    
    clock_t start_time = clock();
    
    // Use smaller scale for CI testing to keep within 5s limit
    // Full scale: 8,388,608 words (1M leaves) - too slow for CI
    // CI scale: 1,048,576 words (128K leaves) - manageable
    const size_t scale_factor = 8;  // Reduce by factor of 8
    const size_t num_words = 8388608 / scale_factor;  // 1,048,576 words
    const size_t num_leaves = num_words / MERKLE_LEAF_WORDS;  // 131,072 leaves
    
    printf("Testing with %zu words (%zu leaves, ~%.1f MiB)\n", 
           num_words, num_leaves, (num_words * 16.0) / (1024 * 1024));
    
    // Allocate test data
    printf("Allocating memory...\n");
    gf128_t *test_data = aligned_alloc(64, num_words * sizeof(gf128_t));
    if (!test_data) {
        printf("FAIL: Memory allocation failed\n");
        return 1;
    }
    
    // Fill with deterministic random data
    printf("Filling with test data...\n");
    for (size_t i = 0; i < num_words; ++i) {
        test_data[i] = random_gf128();
    }
    
    clock_t data_time = clock();
    printf("Data preparation: %.3f seconds\n", 
           ((double)(data_time - start_time)) / CLOCKS_PER_SEC);
    
    // Build tree
    printf("Building Merkle tree...\n");
    merkle_tree_t tree;
    if (merkle_build(test_data, (uint32_t)num_leaves, &tree) != 0) {
        printf("FAIL: Tree build failed\n");
        free(test_data);
        return 1;
    }
    
    clock_t build_time = clock();
    printf("Tree build: %.3f seconds\n", 
           ((double)(build_time - data_time)) / CLOCKS_PER_SEC);
    
    printf("Tree: depth=%u, leaves=%u\n", tree.depth, tree.leaves);
    printf("Root: ");
    for (int i = 0; i < 8; ++i) {
        printf("%02x", tree.root[i]);
    }
    printf("...\n");
    
    // Test opening 100 random leaves (without using insecure verify)
    printf("Testing 100 random leaf openings...\n");
    const int num_tests = 100;
    int success_count = 0;
    
    for (int i = 0; i < num_tests; ++i) {
        uint32_t leaf_idx = test_rand() % tree.leaves;
        gf128_t value;
        uint8_t path[30 * 32];
        
        // Open leaf (test that opening works, secure verification tested elsewhere)
        if (merkle_open(&tree, test_data, leaf_idx, &value, path) == 0) {
            success_count++;
        } else {
            printf("FAIL: Opening failed for leaf %u\n", leaf_idx);
            break;
        }
        
        // Progress indicator
        if ((i + 1) % 25 == 0) {
            printf("  Completed %d/%d tests\n", i + 1, num_tests);
        }
    }
    
    clock_t test_time = clock();
    printf("Leaf testing: %.3f seconds\n", 
           ((double)(test_time - build_time)) / CLOCKS_PER_SEC);
    
    free(test_data);
    
    clock_t total_time = clock();
    double elapsed = ((double)(total_time - start_time)) / CLOCKS_PER_SEC;
    
    printf("\n=== Results ===\n");
    printf("Total time: %.3f seconds\n", elapsed);
    printf("Opened leaves: %d/%d\n", success_count, num_tests);
    
    if (success_count == num_tests && elapsed <= 5.0) {
        printf("✅ PASS: All tests completed within time limit\n");
        
        // Performance summary
        printf("\nPerformance Summary:\n");
        printf("- Tree build rate: %.1f leaves/second\n", 
               tree.leaves / ((double)(build_time - data_time) / CLOCKS_PER_SEC));
        printf("- Opening rate: %.1f leaves/second\n",
               num_tests / ((double)(test_time - build_time) / CLOCKS_PER_SEC));
        
        return 0;
    } else {
        if (success_count != num_tests) {
            printf("❌ FAIL: %d/%d tests failed\n", num_tests - success_count, num_tests);
        }
        if (elapsed > 5.0) {
            printf("❌ FAIL: Test took %.3f seconds (>5s limit)\n", elapsed);
        }
        return 1;
    }
}