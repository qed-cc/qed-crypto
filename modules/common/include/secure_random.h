#ifndef SECURE_RANDOM_H
#define SECURE_RANDOM_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/**
 * @file secure_random.h
 * @brief Cryptographically secure random number generation
 * 
 * This module provides secure random number generation using the best
 * available entropy source on the current platform. It tries multiple
 * sources in order of preference:
 * 1. getrandom() system call (Linux 3.17+)
 * 2. /dev/urandom device
 * 3. Emergency fallback (NOT cryptographically secure)
 */

// Return codes for random generation functions
typedef enum {
    SECURE_RANDOM_SUCCESS = 0,        // Successfully generated random bytes
    SECURE_RANDOM_UNAVAILABLE = -1,   // No secure source available
    SECURE_RANDOM_PARTIAL = -2,       // Only partial data generated
    SECURE_RANDOM_FAILED = -3         // Generation failed completely
} secure_random_result_t;

/**
 * @brief Generate cryptographically secure random bytes
 * 
 * This is the main interface for secure random generation. It automatically
 * selects the best available entropy source and fills the buffer.
 * 
 * @param buf Buffer to fill with random bytes
 * @param len Number of bytes to generate
 * @return SECURE_RANDOM_SUCCESS on success, error code on failure
 * 
 * @warning If this function fails, the buffer contents are undefined.
 *          Do not use the buffer contents if this function returns an error.
 */
secure_random_result_t secure_random_bytes(void *buf, size_t len);

/**
 * @brief Generate random bytes using getrandom() system call
 * 
 * Uses the getrandom() system call available on Linux 3.17+.
 * This is the preferred method as it's designed specifically for 
 * cryptographic applications.
 * 
 * @param buf Buffer to fill
 * @param len Number of bytes to generate
 * @return Result code
 */
secure_random_result_t secure_random_getrandom(void *buf, size_t len);

/**
 * @brief Generate random bytes from /dev/urandom
 * 
 * Reads from /dev/urandom device. This is widely available on Unix-like
 * systems and provides good cryptographic randomness.
 * 
 * @param buf Buffer to fill
 * @param len Number of bytes to generate
 * @return Result code
 */
secure_random_result_t secure_random_dev_urandom(void *buf, size_t len);

/**
 * @brief Emergency fallback random generation
 * 
 * @warning THIS IS NOT CRYPTOGRAPHICALLY SECURE!
 * Only use when no other entropy sources are available.
 * Uses time, PID, and memory addresses as weak entropy.
 * 
 * @param buf Buffer to fill
 * @param len Number of bytes to generate
 * @return SECURE_RANDOM_SUCCESS (always succeeds)
 */
secure_random_result_t secure_random_fallback(void *buf, size_t len);

/**
 * @brief Check if secure random generation is available
 * 
 * Tests whether at least one secure entropy source is available
 * on the current system.
 * 
 * @return true if secure random is available, false otherwise
 */
bool secure_random_available(void);

/**
 * @brief Get the name of the currently used entropy source
 * 
 * Returns a string describing which entropy source was used for
 * the last call to secure_random_bytes().
 * 
 * @return String name of the entropy source
 */
const char* secure_random_source_name(void);

/**
 * @brief Test entropy sources and print diagnostics
 * 
 * Tests all available entropy sources and prints information about
 * their availability and basic quality checks. Useful for debugging
 * and system validation.
 */
void secure_random_test_entropy(void);

/**
 * @brief Convenience function to generate a 16-byte seed
 * 
 * Common pattern for cryptographic seed generation.
 * 
 * @param seed Buffer of exactly 16 bytes
 * @return true on success, false on failure
 */
static inline bool secure_random_seed_16(uint8_t seed[16]) {
    return secure_random_bytes(seed, 16) == SECURE_RANDOM_SUCCESS;
}

/**
 * @brief Fast paranoid 16-byte seed generation
 * 
 * Combines multiple entropy sources for defense-in-depth:
 * - System random (required)
 * - High-resolution timestamps
 * - CPU hardware RNG (if available)
 * - Process/memory entropy
 * 
 * Adds < 100 microseconds overhead (< 1% impact on proof generation).
 * Even if one source is compromised, others provide entropy.
 * 
 * @param seed Buffer of exactly 16 bytes
 * @return true if at least 2 sources succeeded, false otherwise
 */
bool secure_random_seed_16_safe(uint8_t seed[16]);

/**
 * @brief Generate a 128-byte random seed using paranoid multi-source approach
 * 
 * This function combines multiple entropy sources for defense-in-depth,
 * generating 1024 bits of entropy for maximum paranoid security.
 * Uses the same multi-source approach as seed_16_safe but for more data.
 * 
 * @param seed Output buffer for 128-byte seed
 * @return true on success, false on failure
 */
bool secure_random_seed_128_safe(uint8_t seed[128]);

/**
 * @brief Convenience function to generate a 32-byte seed
 * 
 * Common pattern for cryptographic seed generation.
 * 
 * @param seed Buffer of exactly 32 bytes
 * @return true on success, false on failure
 */
static inline bool secure_random_seed_32(uint8_t seed[32]) {
    return secure_random_bytes(seed, 32) == SECURE_RANDOM_SUCCESS;
}

/**
 * @brief Statistics about entropy source usage
 */
typedef struct {
    int total_calls;          /**< Total calls to secure_random_bytes */
    size_t total_bytes;       /**< Total bytes generated */
    int sources_available;    /**< Number of entropy sources available */
    int sources_used;         /**< Number of unique sources used */
} secure_random_stats_t;

/**
 * @brief Get statistics about entropy generation
 * 
 * @param stats Output statistics structure
 */
void secure_random_get_stats(secure_random_stats_t *stats);

/**
 * @brief Perform self-test of random generation
 * 
 * Tests that:
 * - Random generation works
 * - Consecutive calls produce different output
 * - Multiple entropy sources are available
 * 
 * @return true if all tests pass
 */
bool secure_random_self_test(void);

#endif // SECURE_RANDOM_H