#include "enc.h"
#include "gf128.h"
#include "test_random.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// Generate random GF(128) element
static gf128_t random_gf128() {
    gf128_t result;
    test_random_bytes(&result, sizeof(result));
    return result;
}

// Test encoding/decoding round-trip for small size
static int test_small_roundtrip() {
    const size_t d = 4;  // 16 rows = 64 words
    const size_t n = 1 << (d + 2);  // 64 words
    
    printf("Testing small round-trip (d=%zu, n=%zu words)...\n", d, n);
    
    // Allocate and initialize test data
    gf128_t *original = aligned_alloc(64, n * sizeof(gf128_t));
    gf128_t *working = aligned_alloc(64, n * sizeof(gf128_t));
    
    if (!original || !working) {
        printf("FAIL: Memory allocation failed\n");
        free(original);
        free(working);
        return 0;
    }
    
    // Fill with random data
    for (size_t i = 0; i < n; ++i) {
        original[i] = random_gf128();
        working[i] = original[i];
    }
    
    // Initialize encoder with zero transcript (deterministic tweaks)
    uint8_t zero_transcript[32] = {0};
    enc_init(zero_transcript);
    
    // Encode
    enc_fold(d, working);
    
    // Decode back
    enc_decode(d, working);
    
    // Check round-trip accuracy
    int pass = 1;
    for (size_t i = 0; i < n; ++i) {
        if (!gf128_eq(original[i], working[i])) {
            printf("FAIL: Mismatch at index %zu\n", i);
            pass = 0;
            break;
        }
    }
    
    free(original);
    free(working);
    
    if (pass) {
        printf("PASS: Small round-trip test\n");
    }
    
    return pass;
}

// Test with different transcript roots (zero tweak avoidance)
static int test_zero_tweak_avoidance() {
    printf("Testing zero tweak avoidance...\n");
    
    int all_nonzero = 1;
    
    // Test 1000 different roots
    for (int trial = 0; trial < 1000; ++trial) {
        uint8_t root[32];
        for (int i = 0; i < 32; ++i) {
            test_random_bytes(&root[i], 1);
        }
        
        enc_init(root);
        
        // Check all tweaks are non-zero
        for (size_t j = 0; j < D; ++j) {
            gf128_t tweak = enc_get_tweak(j);
            if (gf128_is_zero(tweak)) {
                printf("FAIL: Zero tweak found at round %zu, trial %d\n", j, trial);
                all_nonzero = 0;
                break;
            }
        }
        
        if (!all_nonzero) break;
    }
    
    if (all_nonzero) {
        printf("PASS: Zero tweak avoidance test\n");
    }
    
    return all_nonzero;
}

// Test medium-size encoding (performance check)
static int test_medium_size() {
    const size_t d = 10;  // 1K rows = 4K words = 64 KiB
    const size_t n = 1 << (d + 2);
    
    printf("Testing medium size (d=%zu, n=%zu words = %zu KiB)...\n", 
           d, n, (n * 16) / 1024);
    
    gf128_t *buf = aligned_alloc(64, n * sizeof(gf128_t));
    if (!buf) {
        printf("FAIL: Memory allocation failed\n");
        return 0;
    }
    
    // Fill with simple pattern
    for (size_t i = 0; i < n; ++i) {
        gf128_t val = {0, i + 1};  // Non-zero values: lo = i+1, hi = 0
        buf[i] = val;
    }
    
    uint8_t test_root[32];
    memset(test_root, 0x42, 32);  // Non-zero root
    enc_init(test_root);
    
    // Encode
    enc_fold(d, buf);
    
    // Simple sanity check: encoded result should be different
    int changed = 0;
    for (size_t i = 0; i < n && !changed; ++i) {
        gf128_t expected = {0, i + 1};
        if (!gf128_eq(buf[i], expected)) {
            changed = 1;
        }
    }
    
    free(buf);
    
    if (changed) {
        printf("PASS: Medium size encoding test\n");
        return 1;
    } else {
        printf("FAIL: Encoding produced no change (unexpected)\n");
        return 0;
    }
}

int main() {
    printf("=== Reed-Muller Encoding Round-trip Tests ===\n\n");
    
    int tests_passed = 0;
    int total_tests = 3;
    
    tests_passed += test_small_roundtrip();
    tests_passed += test_zero_tweak_avoidance();
    tests_passed += test_medium_size();
    
    printf("\n=== Test Summary ===\n");
    printf("Passed: %d/%d tests\n", tests_passed, total_tests);
    
    if (tests_passed == total_tests) {
        printf("All tests PASSED\n");
        return 0;
    } else {
        printf("Some tests FAILED\n");
        return 1;
    }
}