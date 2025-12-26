/**
 * @file secure_random_enhanced.c
 * @brief Enhanced secure random generation with multiple entropy sources
 * 
 * This implementation uses multiple sources of randomness and generates
 * more bits than needed for added security without compromising performance.
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
#include <sys/types.h>
#include <sys/stat.h>

#ifdef __linux__
#include <sys/random.h>
#include <sys/syscall.h>
#include <linux/random.h>
#ifndef GRND_NONBLOCK
#define GRND_NONBLOCK 0x01
#endif
#endif

#ifdef _WIN32
#include <windows.h>
#include <wincrypt.h>
#include <bcrypt.h>
#pragma comment(lib, "bcrypt.lib")
#endif

// XOR mixing buffer size - generate 2x the requested amount
#define ENTROPY_MULTIPLIER 2

// Entropy sources used
typedef enum {
    ENTROPY_GETRANDOM = 1 << 0,
    ENTROPY_URANDOM = 1 << 1,
    ENTROPY_RDRAND = 1 << 2,
    ENTROPY_TIMING = 1 << 3,
    ENTROPY_WINDOWS = 1 << 4
} entropy_source_t;

static int g_entropy_sources_used = 0;
static int g_total_entropy_calls = 0;
static size_t g_total_entropy_bytes = 0;

// Check if RDRAND instruction is available
#ifdef __x86_64__
static int has_rdrand(void) {
    unsigned int eax, ebx, ecx, edx;
    __asm__ volatile("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(1));
    return (ecx & (1 << 30)) != 0;  // RDRAND is bit 30 of ECX
}

// Generate random bytes using RDRAND
static int rdrand_bytes(void *buf, size_t len) {
    if (!has_rdrand()) {
        return -1;
    }
    
    unsigned char *p = (unsigned char *)buf;
    size_t remaining = len;
    
    while (remaining >= 8) {
        uint64_t val;
        int retries = 10;
        int success = 0;
        
        // RDRAND can fail temporarily, retry a few times
        while (retries-- > 0) {
            unsigned char ok;
            __asm__ volatile("rdrand %0; setc %1" : "=r"(val), "=qm"(ok));
            if (ok) {
                success = 1;
                break;
            }
        }
        
        if (!success) {
            return -1;
        }
        
        memcpy(p, &val, 8);
        p += 8;
        remaining -= 8;
    }
    
    // Handle remaining bytes
    if (remaining > 0) {
        uint64_t val;
        int retries = 10;
        int success = 0;
        
        while (retries-- > 0) {
            unsigned char ok;
            __asm__ volatile("rdrand %0; setc %1" : "=r"(val), "=qm"(ok));
            if (ok) {
                success = 1;
                break;
            }
        }
        
        if (!success) {
            return -1;
        }
        
        memcpy(p, &val, remaining);
    }
    
    return 0;
}
#endif

// High-resolution timing entropy (supplemental only)
static void add_timing_entropy(void *buf, size_t len) {
    struct timespec ts;
    unsigned char *p = (unsigned char *)buf;
    
    for (size_t i = 0; i < len; i++) {
        clock_gettime(CLOCK_MONOTONIC, &ts);
        // Use lower bits of nanoseconds which change rapidly
        p[i] ^= (unsigned char)(ts.tv_nsec & 0xFF);
        
        // Add some CPU noise
        volatile unsigned long counter = 0;
        for (int j = 0; j < 100; j++) {
            counter++;
        }
        p[i] ^= (unsigned char)(counter & 0xFF);
    }
}

// Mix two buffers using XOR
static void xor_mix(void *dest, const void *src, size_t len) {
    unsigned char *d = (unsigned char *)dest;
    const unsigned char *s = (const unsigned char *)src;
    
    for (size_t i = 0; i < len; i++) {
        d[i] ^= s[i];
    }
}

// Linux implementation using multiple sources
#ifdef __linux__
secure_random_result_t secure_random_getrandom(void *buf, size_t len) {
    // Generate extra entropy
    size_t total_len = len * ENTROPY_MULTIPLIER;
    unsigned char *extra_buf = malloc(total_len);
    if (!extra_buf) {
        return SECURE_RANDOM_FAILED;
    }
    
    memset(extra_buf, 0, total_len);
    int sources_used = 0;
    int primary_success = 0;
    
    // Primary source: getrandom()
    size_t got = 0;
    while (got < len) {
        ssize_t ret = syscall(SYS_getrandom, (char*)buf + got, len - got, 0);
        if (ret < 0) {
            if (errno == EINTR) continue;
            LOG_DEBUG("secure_random", "getrandom() failed: %s", strerror(errno));
            break;
        }
        got += ret;
    }
    
    if (got == len) {
        primary_success = 1;
        sources_used |= ENTROPY_GETRANDOM;
    }
    
    // Secondary source: /dev/urandom (always try for defense in depth)
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd >= 0) {
        size_t extra_got = 0;
        while (extra_got < total_len) {
            ssize_t ret = read(fd, extra_buf + extra_got, total_len - extra_got);
            if (ret <= 0) break;
            extra_got += ret;
        }
        close(fd);
        
        if (extra_got > 0) {
            sources_used |= ENTROPY_URANDOM;
            if (!primary_success) {
                // Use urandom as primary if getrandom failed
                memcpy(buf, extra_buf, len);
                primary_success = 1;
            } else {
                // Mix with existing entropy
                xor_mix(buf, extra_buf, len);
            }
        }
    }
    
    #ifdef __x86_64__
    // Hardware RNG if available
    if (has_rdrand()) {
        if (rdrand_bytes(extra_buf, len) == 0) {
            sources_used |= ENTROPY_RDRAND;
            xor_mix(buf, extra_buf, len);
        }
    }
    #endif
    
    // Always add timing entropy as final mix
    add_timing_entropy(extra_buf, len);
    xor_mix(buf, extra_buf, len);
    sources_used |= ENTROPY_TIMING;
    
    // Clear sensitive data
    memset(extra_buf, 0, total_len);
    free(extra_buf);
    
    // Update statistics
    g_entropy_sources_used |= sources_used;
    g_total_entropy_calls++;
    g_total_entropy_bytes += len;
    
    LOG_DEBUG("secure_random", "Generated %zu bytes using %d sources", len, __builtin_popcount(sources_used));
    
    return primary_success ? SECURE_RANDOM_SUCCESS : SECURE_RANDOM_FAILED;
}
#endif

// Windows implementation
#ifdef _WIN32
secure_random_result_t secure_random_windows(void *buf, size_t len) {
    // Try BCryptGenRandom first (Vista+)
    NTSTATUS status = BCryptGenRandom(NULL, (PUCHAR)buf, (ULONG)len, BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    if (status == 0) {
        g_entropy_sources_used |= ENTROPY_WINDOWS;
        
        // Add timing entropy for defense in depth
        unsigned char *extra_buf = malloc(len);
        if (extra_buf) {
            add_timing_entropy(extra_buf, len);
            xor_mix(buf, extra_buf, len);
            memset(extra_buf, 0, len);
            free(extra_buf);
            g_entropy_sources_used |= ENTROPY_TIMING;
        }
        
        return SECURE_RANDOM_SUCCESS;
    }
    
    // Fallback to CryptGenRandom
    HCRYPTPROV hProv = 0;
    if (!CryptAcquireContext(&hProv, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT)) {
        return SECURE_RANDOM_FAILED;
    }
    
    BOOL result = CryptGenRandom(hProv, (DWORD)len, (BYTE*)buf);
    CryptReleaseContext(hProv, 0);
    
    if (result) {
        g_entropy_sources_used |= ENTROPY_WINDOWS;
        return SECURE_RANDOM_SUCCESS;
    }
    
    return SECURE_RANDOM_FAILED;
}
#endif

// Main entry point
secure_random_result_t secure_random_bytes(void *buf, size_t len) {
    if (!buf || len == 0) {
        return SECURE_RANDOM_FAILED;
    }
    
    // Clear buffer first
    memset(buf, 0, len);
    
#ifdef __linux__
    return secure_random_getrandom(buf, len);
#elif defined(_WIN32)
    return secure_random_windows(buf, len);
#else
    // Fallback to urandom on other Unix systems
    return secure_random_dev_urandom(buf, len);
#endif
}

// Get entropy statistics
void secure_random_get_stats(secure_random_stats_t *stats) {
    if (!stats) return;
    
    stats->total_calls = g_total_entropy_calls;
    stats->total_bytes = g_total_entropy_bytes;
    stats->sources_available = 0;
    stats->sources_used = 0;
    
    // Count available sources
#ifdef __linux__
    stats->sources_available++;  // getrandom
    if (access("/dev/urandom", R_OK) == 0) stats->sources_available++;
    #ifdef __x86_64__
    if (has_rdrand()) stats->sources_available++;
    #endif
#endif
#ifdef _WIN32
    stats->sources_available += 2;  // BCrypt + CryptGenRandom
#endif
    stats->sources_available++;  // Timing always available
    
    // Count used sources
    stats->sources_used = __builtin_popcount(g_entropy_sources_used);
    
    LOG_INFO("secure_random", "Entropy stats: %d/%d sources used, %zu bytes generated",
             stats->sources_used, stats->sources_available, stats->total_bytes);
}

// Self-test function
bool secure_random_self_test(void) {
    unsigned char buf1[32], buf2[32];
    
    // Test basic generation
    if (secure_random_bytes(buf1, sizeof(buf1)) != SECURE_RANDOM_SUCCESS) {
        LOG_ERROR("secure_random", "Self-test failed: unable to generate random bytes");
        return false;
    }
    
    // Test uniqueness
    if (secure_random_bytes(buf2, sizeof(buf2)) != SECURE_RANDOM_SUCCESS) {
        LOG_ERROR("secure_random", "Self-test failed: unable to generate second buffer");
        return false;
    }
    
    if (memcmp(buf1, buf2, sizeof(buf1)) == 0) {
        LOG_ERROR("secure_random", "Self-test failed: consecutive calls returned identical data");
        return false;
    }
    
    // Test statistics
    secure_random_stats_t stats;
    secure_random_get_stats(&stats);
    
    LOG_INFO("secure_random", "Self-test passed: %d entropy sources available",
             stats.sources_available);
    
    return true;
}

// /dev/urandom implementation
secure_random_result_t secure_random_dev_urandom(void *buf, size_t len) {
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        return SECURE_RANDOM_UNAVAILABLE;
    }
    
    size_t got = 0;
    while (got < len) {
        ssize_t ret = read(fd, (char*)buf + got, len - got);
        if (ret < 0) {
            if (errno == EINTR) continue;
            close(fd);
            return SECURE_RANDOM_FAILED;
        }
        if (ret == 0) {
            close(fd);
            return SECURE_RANDOM_PARTIAL;
        }
        got += ret;
    }
    
    close(fd);
    return SECURE_RANDOM_SUCCESS;
}

// Check if secure random is available
bool secure_random_available(void) {
#ifdef __linux__
    // Try getrandom
    unsigned char test;
    if (syscall(SYS_getrandom, &test, 1, GRND_NONBLOCK) >= 0) {
        return true;
    }
#endif
    // Try /dev/urandom
    if (access("/dev/urandom", R_OK) == 0) {
        return true;
    }
    return false;
}

// Get source name
const char* secure_random_source_name(void) {
    static char source_desc[256];
    int count = __builtin_popcount(g_entropy_sources_used);
    
    if (count == 0) {
        return "none";
    } else if (count == 1) {
        if (g_entropy_sources_used & ENTROPY_GETRANDOM) return "getrandom";
        if (g_entropy_sources_used & ENTROPY_URANDOM) return "urandom";
        if (g_entropy_sources_used & ENTROPY_RDRAND) return "rdrand";
        if (g_entropy_sources_used & ENTROPY_WINDOWS) return "windows";
        if (g_entropy_sources_used & ENTROPY_TIMING) return "timing";
    }
    
    snprintf(source_desc, sizeof(source_desc), "mixed (%d sources)", count);
    return source_desc;
}

// Test entropy sources
void secure_random_test_entropy(void) {
    printf("Testing entropy sources...\n");
    
#ifdef __linux__
    // Test getrandom
    unsigned char test[16];
    if (syscall(SYS_getrandom, test, sizeof(test), GRND_NONBLOCK) >= 0) {
        printf("  getrandom(): AVAILABLE\n");
    } else {
        printf("  getrandom(): NOT AVAILABLE (%s)\n", strerror(errno));
    }
    
    // Test /dev/urandom
    if (access("/dev/urandom", R_OK) == 0) {
        printf("  /dev/urandom: AVAILABLE\n");
    } else {
        printf("  /dev/urandom: NOT AVAILABLE\n");
    }
    
#ifdef __x86_64__
    // Test RDRAND
    if (has_rdrand()) {
        printf("  RDRAND: AVAILABLE\n");
    } else {
        printf("  RDRAND: NOT AVAILABLE\n");
    }
#endif
#endif
    
    printf("  Timing entropy: ALWAYS AVAILABLE\n");
    
    // Run self-test
    if (secure_random_self_test()) {
        printf("\nSelf-test: PASSED\n");
    } else {
        printf("\nSelf-test: FAILED\n");
    }
}

// Fallback implementation (NOT SECURE)
secure_random_result_t secure_random_fallback(void *buf, size_t len) {
    LOG_WARN("secure_random", "Using INSECURE fallback random generator!");
    
    unsigned char *p = (unsigned char *)buf;
    
    // Mix multiple weak sources
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    
    uint64_t seed = ts.tv_sec ^ ts.tv_nsec ^ getpid() ^ (uintptr_t)buf;
    
    // Simple PRNG
    for (size_t i = 0; i < len; i++) {
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        p[i] = (unsigned char)(seed >> 32);
    }
    
    return SECURE_RANDOM_SUCCESS;
}

/**
 * @brief Fast paranoid 16-byte seed generation
 * 
 * Combines multiple entropy sources efficiently:
 * - Primary: System random (getrandom/urandom)
 * - Secondary: CPU RDRAND (if available)
 * - Tertiary: High-resolution timestamps
 * - Quaternary: Process/memory addresses
 * 
 * All sources XORed together. Adds < 100 microseconds overhead.
 */
bool secure_random_seed_16_safe(uint8_t seed[16]) {
    uint8_t entropy[16] = {0};
    int sources = 0;
    
    // Track timing for performance
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    // Source 1: System random (primary, required)
    if (secure_random_bytes(seed, 16) == SECURE_RANDOM_SUCCESS) {
        sources++;
        // Start with system random
        memcpy(entropy, seed, 16);
    } else {
        return false;  // Must have system random
    }
    
    // Source 2: High-res timestamp (always available, very fast)
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t time_entropy = ts.tv_nsec ^ (ts.tv_sec * 0x9e3779b97f4a7c15ULL);
    
    // Also use monotonic time
    clock_gettime(CLOCK_MONOTONIC, &ts);
    time_entropy ^= ts.tv_nsec ^ (ts.tv_sec * 0xc6a4a7935bd1e995ULL);
    
    // XOR time into entropy
    for (int i = 0; i < 8; i++) {
        entropy[i] ^= (time_entropy >> (i * 8)) & 0xFF;
        entropy[i + 8] ^= (time_entropy >> ((7-i) * 8)) & 0xFF;
    }
    sources++;
    
#ifdef __x86_64__
    // Source 3: RDRAND if available (very fast on modern CPUs)
    if (has_rdrand()) {
        uint64_t rdrand_val;
        if (_rdrand64_step(&rdrand_val)) {
            for (int i = 0; i < 8; i++) {
                entropy[i] ^= (rdrand_val >> (i * 8)) & 0xFF;
            }
            if (_rdrand64_step(&rdrand_val)) {
                for (int i = 0; i < 8; i++) {
                    entropy[i + 8] ^= (rdrand_val >> (i * 8)) & 0xFF;
                }
            }
            sources++;
        }
    }
    
    // Source 4: TSC (Time Stamp Counter) - extremely fast
    uint64_t tsc = __rdtsc();
    entropy[0] ^= tsc & 0xFF;
    entropy[8] ^= (tsc >> 32) & 0xFF;
#endif
    
    // Source 5: Process entropy (fast)
    pid_t pid = getpid();
    uint64_t stack_addr = (uint64_t)&entropy;
    uint64_t heap_addr = (uint64_t)malloc(1);
    
    uint64_t proc_entropy = pid ^ stack_addr ^ heap_addr;
    entropy[1] ^= proc_entropy & 0xFF;
    entropy[9] ^= (proc_entropy >> 32) & 0xFF;
    
    if (heap_addr) free((void*)heap_addr);
    sources++;
    
    // Copy final mixed entropy to output
    memcpy(seed, entropy, 16);
    
    // Measure time taken
    clock_gettime(CLOCK_MONOTONIC, &end);
    long ns = (end.tv_sec - start.tv_sec) * 1000000000L + (end.tv_nsec - start.tv_nsec);
    
    // Log if too slow (> 100 microseconds)
    if (ns > 100000) {
        LOG_DEBUG("secure_random_seed_16_safe took %ld ns (%d sources)", ns, sources);
    }
    
    // Clear sensitive data
    memset(entropy, 0, sizeof(entropy));
    
    return sources >= 2;  // Success if we have system + at least one other source
}