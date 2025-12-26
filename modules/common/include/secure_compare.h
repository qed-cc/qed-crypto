/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef SECURE_COMPARE_H
#define SECURE_COMPARE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/**
 * @file secure_compare.h
 * @brief Constant-time comparison functions for cryptographic operations
 * 
 * These functions prevent timing attacks by ensuring comparisons take
 * the same amount of time regardless of where differences occur.
 */

/**
 * @brief Constant-time memory comparison
 * 
 * @param a First buffer to compare
 * @param b Second buffer to compare  
 * @param n Number of bytes to compare
 * @return 0 if equal, non-zero if different
 */
static inline int secure_memcmp(const void *a, const void *b, size_t n) {
    const uint8_t *_a = (const uint8_t *)a;
    const uint8_t *_b = (const uint8_t *)b;
    uint8_t result = 0;
    
    for (size_t i = 0; i < n; i++) {
        result |= _a[i] ^ _b[i];
    }
    
    /* Convert to standard memcmp return value */
    return (int)result;
}

/**
 * @brief Constant-time 32-byte comparison (optimized for SHA3-256)
 * 
 * @param a First 32-byte buffer
 * @param b Second 32-byte buffer
 * @return 0 if equal, non-zero if different
 */
static inline int secure_cmp32(const void *a, const void *b) {
    const uint64_t *_a = (const uint64_t *)a;
    const uint64_t *_b = (const uint64_t *)b;
    uint64_t result = 0;
    
    /* Unrolled for 32 bytes (4 * 8 bytes) */
    result |= _a[0] ^ _b[0];
    result |= _a[1] ^ _b[1];
    result |= _a[2] ^ _b[2];
    result |= _a[3] ^ _b[3];
    
    /* Reduce to single value */
    result |= result >> 32;
    result |= result >> 16;
    result |= result >> 8;
    
    return (int)(result & 0xFF);
}

/**
 * @brief Constant-time equality check
 * 
 * @param a First buffer to compare
 * @param b Second buffer to compare
 * @param n Number of bytes to compare
 * @return true if equal, false if different
 */
static inline bool secure_memeq(const void *a, const void *b, size_t n) {
    return secure_memcmp(a, b, n) == 0;
}

/**
 * @brief Constant-time select between two values
 * 
 * @param condition If 0, return a. If non-zero, return b.
 * @param a Value to return if condition is 0
 * @param b Value to return if condition is non-zero
 * @return Selected value
 */
static inline uint32_t secure_select_u32(uint32_t condition, uint32_t a, uint32_t b) {
    /* Create a mask that's all 1s if condition != 0, all 0s if condition == 0 */
    uint32_t mask = (uint32_t)(-(condition != 0));
    return (a & ~mask) | (b & mask);
}

/**
 * @brief Constant-time conditional copy
 * 
 * @param dest Destination buffer
 * @param src Source buffer
 * @param n Number of bytes to copy
 * @param condition If non-zero, perform copy. If 0, do nothing.
 */
static inline void secure_conditional_copy(void *dest, const void *src, size_t n, uint32_t condition) {
    uint8_t *_dest = (uint8_t *)dest;
    const uint8_t *_src = (const uint8_t *)src;
    uint8_t mask = (uint8_t)(-(condition != 0));
    
    for (size_t i = 0; i < n; i++) {
        _dest[i] = (_dest[i] & ~mask) | (_src[i] & mask);
    }
}

/**
 * @brief Securely clear memory
 * 
 * This function securely clears memory to prevent sensitive data from
 * persisting after use. It's designed to resist compiler optimization.
 * 
 * @param ptr Pointer to memory to clear
 * @param n Number of bytes to clear
 */
static inline void secure_memzero(void *ptr, size_t n) {
    volatile uint8_t *_ptr = (volatile uint8_t *)ptr;
    
    while (n--) {
        *_ptr++ = 0;
    }
    
    /* Memory barrier to prevent reordering */
    __asm__ __volatile__("" ::: "memory");
}

#endif /* SECURE_COMPARE_H */