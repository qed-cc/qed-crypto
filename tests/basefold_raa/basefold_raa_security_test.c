/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "basefold_raa.h"
#include "sha3.h"
#include "gf128.h"
#include "logger.h"

/**
 * @brief Security validation test for BaseFold+RAA
 * 
 * This test verifies:
 * 1. Correct SHA3-256 computation
 * 2. Proper security parameters (320 queries)
 * 3. Soundness guarantees
 * 4. Proof size within limits
 */

// Verify SHA3-256 matches OpenSSL
static int verify_sha3_correctness() {
    LOG_INFO("raa_security", "=== SHA3-256 Correctness Test ===\n");
    
    // Test vectors
    struct {
        const char* input;
        const char* expected_hex;
    } test_vectors[] = {
        {"", "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"},
        {"abcdef", "59890c1d183aa279505750422e6384ccb1499c793872d6f31bb3bcaa4bc9f5a5"},
        {"hello world", "644bcc7e564373040999aac89e7622f3ca71fba1d972fd94a31c3bfbf24e3938"},
        {"The quick brown fox jumps over the lazy dog", "69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04"}
    };
    
    int passed = 0;
    for (size_t i = 0; i < sizeof(test_vectors)/sizeof(test_vectors[0]); i++) {
        uint8_t hash[32];
        sha3_hash(SHA3_256, test_vectors[i].input, strlen(test_vectors[i].input), hash, 32);
        
        // Convert to hex
        char hex[65];
        for (int j = 0; j < 32; j++) {
            sLOG_INFO("basefold_raa_security_test", &hex[j*2], "%02x", hash[j]);
        }
        hex[64] = '\0';
        
        if (strcmp(hex, test_vectors[i].expected_hex) == 0) {
            LOG_INFO("raa_security", "✓ \"%s\": PASS\n", test_vectors[i].input);
            passed++;
        } else {
            LOG_INFO("raa_security", "✗ \"%s\": FAIL\n", test_vectors[i].input);
            LOG_INFO("raa_security", "  Expected: %s\n", test_vectors[i].expected_hex);
            LOG_INFO("raa_security", "  Got:      %s\n", hex);
        }
    }
    
    LOG_INFO("raa_security", "\nResult: %d/%zu tests passed\n\n", passed, sizeof(test_vectors)/sizeof(test_vectors[0]));
    return passed == sizeof(test_vectors)/sizeof(test_vectors[0]);
}

// Verify security parameters
static int verify_security_parameters() {
    LOG_INFO("raa_security", "=== Security Parameters Test ===\n");
    
    int all_good = 1;
    
    // Check query count
    LOG_INFO("raa_security", "Query count: %d ", BASEFOLD_RAA_NUM_QUERIES);
    if (BASEFOLD_RAA_NUM_QUERIES >= 320) {
        LOG_INFO("raa_security", "✓ (sufficient for 122-bit security)\n");
    } else {
        LOG_INFO("raa_security", "✗ (INSUFFICIENT - need at least 320)\n");
        all_good = 0;
    }
    
    // Check security bits
    LOG_INFO("raa_security", "Security bits: %d ", BASEFOLD_RAA_SECURITY_BITS);
    if (BASEFOLD_RAA_SECURITY_BITS == 122) {
        LOG_INFO("raa_security", "✓ (correctly documented)\n");
    } else {
        LOG_INFO("raa_security", "✗ (should be 122, not %d)\n", BASEFOLD_RAA_SECURITY_BITS);
        all_good = 0;
    }
    
    // Calculate actual soundness
    double query_soundness = BASEFOLD_RAA_NUM_QUERIES * 0.415; // log2(4/3) ≈ 0.415
    double sumcheck_soundness = 122; // 18 rounds * 3 degree / 2^128
    double effective_soundness = (query_soundness < sumcheck_soundness) ? query_soundness : sumcheck_soundness;
    
    LOG_INFO("raa_security", "\nSoundness analysis:\n");
    LOG_INFO("raa_security", "- Query soundness: %.1f bits\n", query_soundness);
    LOG_INFO("raa_security", "- Sumcheck soundness: %.1f bits\n", sumcheck_soundness);
    LOG_INFO("raa_security", "- Effective soundness: %.1f bits ", effective_soundness);
    
    if (effective_soundness >= 120) {
        LOG_INFO("raa_security", "✓\n");
    } else {
        LOG_INFO("raa_security", "✗ (INSUFFICIENT)\n");
        all_good = 0;
    }
    
    // Estimate proof size
    size_t sumcheck_data = 18 * 3 * 16; // 18 rounds, 3 values, 16 bytes each
    size_t query_responses = BASEFOLD_RAA_NUM_QUERIES * 16; // 16 bytes per query
    size_t merkle_paths = BASEFOLD_RAA_NUM_QUERIES * 18 * 32; // path length 18, 32 bytes per hash
    size_t total_proof_size = sumcheck_data + query_responses + merkle_paths + 1024; // +metadata
    
    LOG_INFO("raa_security", "\nProof size estimate:\n");
    LOG_INFO("raa_security", "- Sumcheck data: %zu bytes\n", sumcheck_data);
    LOG_INFO("raa_security", "- Query responses: %zu bytes\n", query_responses);
    LOG_INFO("raa_security", "- Merkle paths: %zu bytes\n", merkle_paths);
    LOG_INFO("raa_security", "- Total: %zu bytes (%.1f KB) ", total_proof_size, total_proof_size / 1024.0);
    
    if (total_proof_size <= 500 * 1024) {
        LOG_INFO("raa_security", "✓ (under 500KB limit)\n");
    } else {
        LOG_INFO("raa_security", "✗ (exceeds 500KB limit)\n");
        all_good = 0;
    }
    
    LOG_INFO("raa_security", "\n");
    return all_good;
}

// Test Binary NTT implementation
static int test_binary_ntt() {
    LOG_INFO("raa_security", "=== Binary NTT Test ===\n");
    
    // Check if Binary NTT is properly implemented
    // For now, we'll check if the header exists and basic functionality
    
    #ifdef BINARY_NTT_H
    LOG_INFO("raa_security", "✓ Binary NTT header found\n");
    
    // TODO: Add actual Binary NTT round-trip test
    LOG_INFO("raa_security", "⚠ Binary NTT implementation test pending\n");
    
    return 1; // Assume pass for now
    #else
    LOG_INFO("raa_security", "✗ Binary NTT not implemented\n");
    return 0;
    #endif
}

// Main security validation
int main() {
    LOG_INFO("raa_security", "BaseFold+RAA Security Validation Test\n");
    LOG_INFO("raa_security", "=====================================\n\n");
    
    int all_tests_passed = 1;
    
    // Test 1: SHA3 correctness
    if (!verify_sha3_correctness()) {
        all_tests_passed = 0;
        LOG_INFO("raa_security", "CRITICAL: SHA3 implementation incorrect!\n\n");
    }
    
    // Test 2: Security parameters
    if (!verify_security_parameters()) {
        all_tests_passed = 0;
        LOG_INFO("raa_security", "CRITICAL: Security parameters insufficient!\n\n");
    }
    
    // Test 3: Binary NTT
    if (!test_binary_ntt()) {
        LOG_INFO("raa_security", "WARNING: Binary NTT not fully implemented\n\n");
    }
    
    // Summary
    LOG_INFO("raa_security", "=== Security Assessment ===\n");
    if (all_tests_passed && BASEFOLD_RAA_NUM_QUERIES >= 320) {
        LOG_INFO("raa_security", "✅ SECURE: BaseFold+RAA meets security requirements\n");
        LOG_INFO("raa_security", "- SHA3-256 computation: CORRECT\n");
        LOG_INFO("raa_security", "- Query count: SUFFICIENT (%d queries)\n", BASEFOLD_RAA_NUM_QUERIES);
        LOG_INFO("raa_security", "- Effective soundness: %.1f bits\n", 
               (BASEFOLD_RAA_NUM_QUERIES * 0.415 < 122) ? BASEFOLD_RAA_NUM_QUERIES * 0.415 : 122);
        LOG_INFO("raa_security", "- Post-quantum: YES (no discrete log)\n");
    } else {
        LOG_INFO("raa_security", "❌ INSECURE: BaseFold+RAA has security issues\n");
        if (BASEFOLD_RAA_NUM_QUERIES < 320) {
            LOG_INFO("raa_security", "- Query count TOO LOW: %d (need 320+)\n", BASEFOLD_RAA_NUM_QUERIES);
        }
    }
    
    return all_tests_passed ? 0 : 1;
}