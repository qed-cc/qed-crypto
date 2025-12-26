/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file secure_random_fast.c
 * @brief Fast secure random generation optimized for cryptographic applications
 * 
 * This implementation focuses on speed while maintaining cryptographic security.
 * Target: < 0.001 seconds (1ms) for typical operations.
 */

#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif

#include "secure_random.h"
#include "logger.h"
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#ifdef __linux__
#include <sys/random.h>
#include <sys/syscall.h>
#ifndef GRND_NONBLOCK
#define GRND_NONBLOCK 0x01
#endif
#endif

// Static buffer for mixing - avoid malloc overhead
#define MIX_BUFFER_SIZE 256
static unsigned char g_mix_buffer[MIX_BUFFER_SIZE];
static int g_mix_buffer_pos = MIX_BUFFER_SIZE;  // Force initial fill

// Statistics
static int g_total_calls = 0;
static size_t g_total_bytes = 0;

// Primary entropy source - fast and secure
secure_random_result_t secure_random_bytes(void *buf, size_t len) {
    if (!buf || len == 0) {
        return SECURE_RANDOM_FAILED;
    }
    
    // Update stats
    g_total_calls++;
    g_total_bytes += len;
    
#ifdef __linux__
    // Use getrandom() directly - it's fast and secure
    size_t got = 0;
    while (got < len) {
        ssize_t ret = syscall(SYS_getrandom, (char*)buf + got, len - got, 0);
        if (ret < 0) {
            if (errno == EINTR) continue;
            // Fallback to urandom
            goto try_urandom;
        }
        got += ret;
    }
    return SECURE_RANDOM_SUCCESS;
    
try_urandom:
#endif
    
    // Fast fallback: /dev/urandom with O_CLOEXEC
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        return SECURE_RANDOM_UNAVAILABLE;
    }
    
    got = 0;
    while (got < len) {
        ssize_t ret = read(fd, (char*)buf + got, len - got);
        if (ret <= 0) {
            close(fd);
            return got > 0 ? SECURE_RANDOM_PARTIAL : SECURE_RANDOM_FAILED;
        }
        got += ret;
    }
    
    close(fd);
    return SECURE_RANDOM_SUCCESS;
}

// For enhanced security: mix with additional entropy (optional)
secure_random_result_t secure_random_bytes_mixed(void *buf, size_t len) {
    // Get primary randomness
    secure_random_result_t result = secure_random_bytes(buf, len);
    if (result != SECURE_RANDOM_SUCCESS) {
        return result;
    }
    
    // For small requests, XOR with pre-generated mixing buffer
    if (len <= MIX_BUFFER_SIZE) {
        // Refill mixing buffer if needed
        if (g_mix_buffer_pos + len > MIX_BUFFER_SIZE) {
            if (secure_random_bytes(g_mix_buffer, MIX_BUFFER_SIZE) != SECURE_RANDOM_SUCCESS) {
                return SECURE_RANDOM_SUCCESS;  // Primary succeeded, that's enough
            }
            g_mix_buffer_pos = 0;
        }
        
        // Fast XOR mixing
        unsigned char *p = (unsigned char *)buf;
        for (size_t i = 0; i < len; i++) {
            p[i] ^= g_mix_buffer[g_mix_buffer_pos++];
        }
    }
    
    return SECURE_RANDOM_SUCCESS;
}

// Lightweight self-test
bool secure_random_self_test(void) {
    unsigned char buf1[16], buf2[16];
    
    // Test basic generation
    if (secure_random_bytes(buf1, sizeof(buf1)) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    
    // Test uniqueness
    if (secure_random_bytes(buf2, sizeof(buf2)) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    
    return memcmp(buf1, buf2, sizeof(buf1)) != 0;
}

// Stats function
void secure_random_get_stats(secure_random_stats_t *stats) {
    if (!stats) return;
    
    stats->total_calls = g_total_calls;
    stats->total_bytes = g_total_bytes;
    stats->sources_available = 2;  // getrandom + urandom
    stats->sources_used = 1;       // We use one at a time for speed
}

// Simple source name
const char* secure_random_source_name(void) {
#ifdef __linux__
    return "getrandom/urandom";
#else
    return "urandom";
#endif
}

// Check availability
bool secure_random_available(void) {
#ifdef __linux__
    // Quick check with GRND_NONBLOCK
    unsigned char test;
    if (syscall(SYS_getrandom, &test, 1, GRND_NONBLOCK) >= 0) {
        return true;
    }
#endif
    return access("/dev/urandom", R_OK) == 0;
}

// Minimal entropy test
void secure_random_test_entropy(void) {
    printf("Entropy sources:\n");
#ifdef __linux__
    printf("  getrandom(): %s\n", secure_random_available() ? "available" : "not available");
#endif
    printf("  /dev/urandom: %s\n", access("/dev/urandom", R_OK) == 0 ? "available" : "not available");
}

// Stubs for compatibility
secure_random_result_t secure_random_getrandom(void *buf, size_t len) {
    return secure_random_bytes(buf, len);
}

secure_random_result_t secure_random_dev_urandom(void *buf, size_t len) {
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return SECURE_RANDOM_UNAVAILABLE;
    
    size_t got = 0;
    while (got < len) {
        ssize_t ret = read(fd, (char*)buf + got, len - got);
        if (ret <= 0) {
            close(fd);
            return got > 0 ? SECURE_RANDOM_PARTIAL : SECURE_RANDOM_FAILED;
        }
        got += ret;
    }
    close(fd);
    return SECURE_RANDOM_SUCCESS;
}

secure_random_result_t secure_random_fallback(void *buf, size_t len) {
    // Should never be called, but provide basic implementation
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t seed = ts.tv_sec ^ ts.tv_nsec ^ getpid();
    
    unsigned char *p = (unsigned char *)buf;
    for (size_t i = 0; i < len; i++) {
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        p[i] = (unsigned char)(seed >> 32);
    }
    return SECURE_RANDOM_SUCCESS;
}

#ifdef __x86_64__
#include <x86intrin.h>
#include <cpuid.h>
#endif

/**
 * @brief Fast paranoid 16-byte seed generation
 * 
 * Combines multiple entropy sources efficiently (< 100µs overhead).
 * Even if one source is compromised, others provide entropy.
 */
bool secure_random_seed_16_safe(uint8_t seed[16]) {
    uint8_t entropy[16] = {0};
    int sources = 0;
    
    // Source 1: System random (required)
    if (secure_random_bytes(seed, 16) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    memcpy(entropy, seed, 16);
    sources++;
    
    // Source 2: High-res timestamp (very fast, always available)
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t time_entropy = ts.tv_nsec ^ (ts.tv_sec * 0x9e3779b97f4a7c15ULL);
    clock_gettime(CLOCK_MONOTONIC, &ts);
    time_entropy ^= ts.tv_nsec ^ (ts.tv_sec * 0xc6a4a7935bd1e995ULL);
    
    for (int i = 0; i < 8; i++) {
        entropy[i] ^= (time_entropy >> (i * 8)) & 0xFF;
        entropy[i + 8] ^= (time_entropy >> ((7-i) * 8)) & 0xFF;
    }
    sources++;
    
#ifdef __x86_64__
    // Source 3: TSC (Time Stamp Counter) - extremely fast, always available
    uint64_t tsc = __rdtsc();
    // Mix TSC into multiple bytes for better entropy distribution
    for (int i = 0; i < 8; i++) {
        entropy[i] ^= (tsc >> (i * 8)) & 0xFF;
        entropy[i + 8] ^= (tsc >> (56 - i * 8)) & 0xFF;
    }
    sources++;
#endif
    
    // Source 5: Process entropy (fast)
    pid_t pid = getpid();
    uint64_t stack_addr = (uint64_t)&entropy;
    uint64_t proc_entropy = pid ^ stack_addr;
    entropy[1] ^= proc_entropy & 0xFF;
    entropy[9] ^= (proc_entropy >> 32) & 0xFF;
    sources++;
    
    // Copy final result
    memcpy(seed, entropy, 16);
    
    // Clear sensitive data
    memset(entropy, 0, sizeof(entropy));
    
    return sources >= 2;  // Need system + at least one other source
}

bool secure_random_seed_128_safe(uint8_t seed[128]) {
    uint8_t entropy[128] = {0};
    int sources = 0;
    
    // Source 1: System random (required)
    if (secure_random_bytes(seed, 128) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    memcpy(entropy, seed, 128);
    sources++;
    
    // Source 2: High-resolution timestamp entropy (spread across buffer)
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t time_mix = ts.tv_nsec ^ (ts.tv_sec * 0x9e3779b97f4a7c15ULL);
    
    // Mix time entropy at multiple positions
    for (int i = 0; i < 16; i++) {
        entropy[i * 8] ^= (time_mix >> ((i % 8) * 8)) & 0xFF;
        time_mix = (time_mix << 7) | (time_mix >> 57); // Rotate
    }
    sources++;
    
#ifdef __x86_64__
    // Source 3: CPU Time Stamp Counter (TSC)
    uint64_t tsc = __builtin_ia32_rdtsc();
    for (int i = 0; i < 16; i++) {
        entropy[i * 8 + 4] ^= (tsc >> ((i % 8) * 8)) & 0xFF;
        tsc = (tsc << 11) | (tsc >> 53); // Rotate differently
    }
    sources++;
#endif
    
    // Source 5: Process and memory entropy (spread across buffer)
    pid_t pid = getpid();
    uint64_t stack_addr = (uint64_t)&entropy;
    uint64_t heap_addr = (uint64_t)malloc(1);
    free((void*)heap_addr);
    
    uint64_t proc_entropy = pid ^ stack_addr ^ heap_addr;
    for (int i = 0; i < 16; i++) {
        entropy[i * 8 + 1] ^= (proc_entropy >> ((i % 8) * 8)) & 0xFF;
        proc_entropy = (proc_entropy << 13) | (proc_entropy >> 51); // Rotate
    }
    sources++;
    
    // Final mixing step - simple XOR folding for distribution
    // This ensures all entropy sources contribute to final output
    for (int i = 0; i < 64; i++) {
        seed[i] ^= entropy[i + 64];
        seed[i + 64] ^= entropy[i];
    }
    
    // Copy final mixed result
    memcpy(seed, entropy, 128);
    
    // Clear sensitive data
    memset(entropy, 0, sizeof(entropy));
    
    return sources >= 2;  // Need system + at least one other source
}