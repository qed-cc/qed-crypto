#ifndef SECURE_RANDOM_COMPAT_H
#define SECURE_RANDOM_COMPAT_H

/**
 * @file secure_random_compat.h
 * @brief Compatibility helpers for migrating from insecure rand() usage
 * 
 * This header provides helper functions and macros to make it easier to
 * migrate from insecure rand() usage to secure random generation.
 */

#include "secure_random.h"
#include <stdio.h>

/**
 * @brief Secure replacement for common rand() seed generation patterns
 * 
 * These functions provide drop-in replacements for common patterns of
 * using rand() to generate cryptographic seeds.
 */

/**
 * @brief Wrapper for secure seed generation with error logging
 * 
 * Uses the paranoid multi-source function defined in secure_random.h
 * 
 * @param seed Buffer of exactly 16 bytes
 * @return true on success, false on failure
 */
static inline bool secure_random_seed_16_compat(uint8_t seed[16]) {
    if (!seed) return false;
    
    // Use the paranoid version from secure_random.h
    bool result = secure_random_seed_16_safe(seed);
    if (!result) {
        fprintf(stderr, "CRITICAL ERROR: Failed to generate secure 16-byte seed\n");
        fprintf(stderr, "This is a security failure - cannot proceed safely\n");
    }
    return result;
}

/**
 * @brief Generate a secure 32-byte seed (replaces common rand() loop)
 * 
 * @param seed Buffer of exactly 32 bytes
 * @return true on success, false on failure
 */
static inline bool secure_random_seed_32_safe(uint8_t seed[32]) {
    if (!seed) return false;
    
    bool result = secure_random_seed_32(seed);
    if (!result) {
        fprintf(stderr, "CRITICAL ERROR: Failed to generate secure 32-byte seed\n");
        fprintf(stderr, "This is a security failure - cannot proceed safely\n");
    }
    return result;
}

/**
 * @brief Generate secure random bytes with error logging
 * 
 * Wrapper around secure_random_bytes() that provides detailed error logging.
 * 
 * @param buf Buffer to fill
 * @param len Number of bytes to generate
 * @return true on success, false on failure
 */
static inline bool secure_random_bytes_safe(void *buf, size_t len) {
    if (!buf || len == 0) {
        fprintf(stderr, "ERROR: Invalid parameters to secure_random_bytes_safe\n");
        return false;
    }
    
    secure_random_result_t result = secure_random_bytes(buf, len);
    
    switch (result) {
        case SECURE_RANDOM_SUCCESS:
            return true;
            
        case SECURE_RANDOM_UNAVAILABLE:
            fprintf(stderr, "CRITICAL ERROR: No secure entropy sources available\n");
            fprintf(stderr, "Cannot generate cryptographically secure random data\n");
            return false;
            
        case SECURE_RANDOM_PARTIAL:
            fprintf(stderr, "CRITICAL ERROR: Only partial random data generated\n");
            fprintf(stderr, "This indicates a serious system problem\n");
            return false;
            
        case SECURE_RANDOM_FAILED:
            fprintf(stderr, "CRITICAL ERROR: Random generation failed completely\n");
            fprintf(stderr, "Entropy source: %s\n", secure_random_source_name());
            return false;
            
        default:
            fprintf(stderr, "CRITICAL ERROR: Unknown error from secure random generation\n");
            return false;
    }
}

/**
 * @brief Deprecated rand() usage marker
 * 
 * Use this macro to mark places where rand() is still being used
 * so they can be identified and fixed.
 */
#define INSECURE_RAND_USAGE() \
    do { \
        static bool warned = false; \
        if (!warned) { \
            fprintf(stderr, "WARNING: Insecure rand() usage at %s:%d\n", \
                    __FILE__, __LINE__); \
            fprintf(stderr, "This should be replaced with secure_random_bytes()\n"); \
            warned = true; \
        } \
    } while(0)

/**
 * @brief Temporarily allow rand() usage with warning
 * 
 * For code that still needs to use rand() temporarily (e.g., non-crypto
 * purposes), this macro provides a way to acknowledge the usage.
 */
#define ACKNOWLEDGED_INSECURE_RAND() \
    do { \
        static bool warned = false; \
        if (!warned) { \
            fprintf(stderr, "INFO: Non-cryptographic rand() usage at %s:%d\n", \
                    __FILE__, __LINE__); \
            warned = true; \
        } \
    } while(0)

/**
 * @brief Check if system has adequate entropy for secure operations
 * 
 * This function performs a comprehensive check of available entropy sources
 * and returns whether the system is suitable for cryptographic operations.
 * 
 * @return true if system has adequate entropy, false otherwise
 */
static inline bool system_has_adequate_entropy(void) {
    // Test if any secure source is available
    if (!secure_random_available()) {
        return false;
    }
    
    // Test that we can actually generate random data
    uint8_t test_data[32];
    if (!secure_random_bytes_safe(test_data, sizeof(test_data))) {
        return false;
    }
    
    // Basic sanity check - not all zeros
    bool all_zero = true;
    for (int i = 0; i < 32; i++) {
        if (test_data[i] != 0) {
            all_zero = false;
            break;
        }
    }
    
    return !all_zero;
}

/**
 * @brief Initialization check for cryptographic operations
 * 
 * Call this function at startup to verify the system is ready for
 * cryptographic operations that require secure randomness.
 * 
 * @return true if system is ready, false if unsafe
 */
static inline bool crypto_system_ready(void) {
    printf("Checking cryptographic system readiness...\n");
    
    if (!system_has_adequate_entropy()) {
        printf("❌ System does not have adequate entropy sources\n");
        printf("   This system is NOT safe for cryptographic operations\n");
        return false;
    }
    
    printf("✅ Cryptographic entropy available: %s\n", secure_random_source_name());
    return true;
}

#endif // SECURE_RANDOM_COMPAT_H