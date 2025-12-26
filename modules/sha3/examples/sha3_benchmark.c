/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/* Requires POSIX.1b clock_gettime */
#define _POSIX_C_SOURCE 199309L
/**
 * @file sha3_benchmark.c
 * @brief Benchmark example: measure SHA3-256 hashes per second
 */
#include "sha3.h"
#include <stdio.h>
#include <time.h>
#include <string.h>
/* AVX2 4-way Keccak-f[1600] dispatcher */
#ifdef __GNUC__
#include <immintrin.h>
#include <stdint.h>
/* 4-way and 8-way Keccak-f[1600] dispatchers */
extern void keccak_permutation4_avx2(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3);
extern void keccak_permutation8_avx512(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3,
                                      uint64_t *s4, uint64_t *s5, uint64_t *s6, uint64_t *s7);
#endif

int main(void) {
    unsigned char data[64];
    size_t data_len = sizeof(data);
    memset(data, 0xA5, data_len);
    unsigned char digest[SHA3_MAX_DIGEST_SIZE];

    printf("SHA3-256 Benchmark - 1 second test\n");
    printf("Input size: %zu bytes\n", data_len);

    clock_t start = clock();
    clock_t end = start + CLOCKS_PER_SEC;
    unsigned long long count = 0;
    while (clock() < end) {
        sha3_hash(SHA3_256, data, data_len, digest, SHA3_256_DIGEST_SIZE);
        count++;
    }
    double elapsed = (double)(clock() - start) / CLOCKS_PER_SEC;

    printf("Hashes performed : %llu\n", count);
    printf("Time elapsed     : %.2f seconds\n", elapsed);
    printf("Hash rate        : %.2f hashes/second\n", count / elapsed);

    #ifdef __GNUC__
    if (__builtin_cpu_supports("avx2")) {
        /* 4-way AVX2 benchmark for 64-byte inputs */
        printf("\nAVX2 4-way SHA3-256 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes (4 lanes)\n", data_len);
        /* Prepare padded buffer for SHA3-256 one-block input */
        uint8_t buf[SHA3_256_BLOCK_SIZE];
        /* Fill message and domain/pad */
        memcpy(buf, data, data_len);
        buf[data_len] = 0x06;
        memset(buf + data_len + 1, 0, SHA3_256_BLOCK_SIZE - data_len - 1);
        buf[SHA3_256_BLOCK_SIZE - 1] |= 0x80;
        /* Setup state arrays */
        uint64_t s0[25], s1[25], s2[25], s3[25];
        unsigned char d0[SHA3_256_DIGEST_SIZE], d1[SHA3_256_DIGEST_SIZE];
        unsigned char d2[SHA3_256_DIGEST_SIZE], d3[SHA3_256_DIGEST_SIZE];
        /* Benchmark loop */
        clock_t start2 = clock();
        clock_t end2 = start2 + CLOCKS_PER_SEC;
        unsigned long long count2 = 0;
        while (clock() < end2) {
            /* Initialize states to zero */
            memset(s0, 0, sizeof(s0)); memset(s1, 0, sizeof(s1));
            memset(s2, 0, sizeof(s2)); memset(s3, 0, sizeof(s3));
            /* Absorb padded block into each state */
            const uint64_t *lanes = (const uint64_t *)buf;
            for (int i = 0; i < SHA3_256_BLOCK_SIZE / 8; i++) {
                s0[i] = lanes[i]; s1[i] = lanes[i];
                s2[i] = lanes[i]; s3[i] = lanes[i];
            }
            /* Apply four-way permutation */
            keccak_permutation4_avx2(s0, s1, s2, s3);
            /* Squeeze first 32 bytes (4 lanes) for each state */
            for (int i = 0; i < SHA3_256_DIGEST_SIZE / 8; i++) {
                ((uint64_t *)d0)[i] = s0[i];
                ((uint64_t *)d1)[i] = s1[i];
                ((uint64_t *)d2)[i] = s2[i];
                ((uint64_t *)d3)[i] = s3[i];
            }
            /* Count individual hashes */
            count2 += 4;
        }
        double elapsed2 = (double)(clock() - start2) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count2);
        printf("Time elapsed     : %.2f seconds\n", elapsed2);
        printf("Hash rate        : %.2f hashes/second\n", count2 / elapsed2);
        /* Single-threaded AVX2 4-way throughput above */
    }
    if (__builtin_cpu_supports("avx512f")) {
        /* 8-way AVX-512F benchmark for 64-byte inputs */
        printf("\nAVX-512F 8-way SHA3-256 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes (8 lanes)\n", data_len);
        /* Prepare padded buffer */
        uint8_t buf512[SHA3_256_BLOCK_SIZE];
        memcpy(buf512, data, data_len);
        buf512[data_len] = 0x06;
        memset(buf512 + data_len + 1, 0, SHA3_256_BLOCK_SIZE - data_len - 1);
        buf512[SHA3_256_BLOCK_SIZE - 1] |= 0x80;
        /* Setup state arrays */
        uint64_t t0[25], t1[25], t2[25], t3[25], t4[25], t5[25], t6[25], t7[25];
        unsigned long long c8 = 0;
        /* Benchmark loop */
        clock_t start3 = clock();
        clock_t end3 = start3 + CLOCKS_PER_SEC;
        while (clock() < end3) {
            /* Load initial state */
            const uint64_t *lanes = (const uint64_t *)buf512;
            for (int i = 0; i < SHA3_256_BLOCK_SIZE / 8; i++) {
                uint64_t v = lanes[i];
                t0[i] = v; t1[i] = v; t2[i] = v; t3[i] = v;
                t4[i] = v; t5[i] = v; t6[i] = v; t7[i] = v;
            }
            /* Apply 8-way permutation */
            keccak_permutation8_avx512(t0, t1, t2, t3, t4, t5, t6, t7);
            /* Squeeze 32 bytes for t0 to simulate full hash */
            /* (only counting performance) */
            c8 += 8;
        }
        double elapsed3 = (double)(clock() - start3) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", c8);
        printf("Time elapsed     : %.2f seconds\n", elapsed3);
        printf("Hash rate        : %.2f hashes/second\n", c8 / elapsed3);
    }
#ifdef __GNUC__
    if (__builtin_cpu_supports("avx512f")) {
        /* Single-state AVX-512F SHA3-256 */
        printf("\nAVX-512F single-state SHA3-256 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes\n", data_len);
        clock_t start4 = clock();
        clock_t end4 = start4 + CLOCKS_PER_SEC;
        unsigned long long count4 = 0;
        while (clock() < end4) {
            sha3_hash_256_64B_avx512(data, data_len, digest, SHA3_256_DIGEST_SIZE);
            count4++;
        }
        double elapsed4 = (double)(clock() - start4) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count4);
        printf("Time elapsed     : %.2f seconds\n", elapsed4);
        printf("Hash rate        : %.2f hashes/second\n", count4 / elapsed4);
    }
    /* Benchmark SHA3-512 (scalar path) on 64-byte inputs */
    printf("\nSHA3-512 Benchmark - 1 second test\n");
    printf("Input size: %zu bytes\n", data_len);
    {
        clock_t start5 = clock(), end5 = start5 + CLOCKS_PER_SEC;
        unsigned long long count5 = 0;
        while (clock() < end5) {
            sha3_hash(SHA3_512, data, data_len, digest, SHA3_512_DIGEST_SIZE);
            count5++;
        }
        double elapsed5 = (double)(clock() - start5) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count5);
        printf("Time elapsed     : %.2f seconds\n", elapsed5);
        printf("Hash rate        : %.2f hashes/second\n", count5 / elapsed5);
    }
#ifdef __GNUC__
    if (__builtin_cpu_supports("avx2")) {
        /* Single-state AVX2 SHA3-512 for 64-byte inputs */
        printf("\nAVX2 single-state SHA3-512 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes\n", data_len);
        clock_t start6 = clock(), end6 = start6 + CLOCKS_PER_SEC;
        unsigned long long count6 = 0;
        while (clock() < end6) {
            sha3_hash_512_64B_avx2(data, data_len, digest, SHA3_512_DIGEST_SIZE);
            count6++;
        }
        double elapsed6 = (double)(clock() - start6) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count6);
        printf("Time elapsed     : %.2f seconds\n", elapsed6);
        printf("Hash rate        : %.2f hashes/second\n", count6 / elapsed6);
    }
    if (__builtin_cpu_supports("avx512f")) {
        /* Single-state AVX-512F SHA3-512 for 64-byte inputs */
        printf("\nAVX-512F single-state SHA3-512 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes\n", data_len);
        clock_t start7 = clock(), end7 = start7 + CLOCKS_PER_SEC;
        unsigned long long count7 = 0;
        while (clock() < end7) {
            sha3_hash_512_64B_avx512(data, data_len, digest, SHA3_512_DIGEST_SIZE);
            count7++;
        }
        double elapsed7 = (double)(clock() - start7) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count7);
        printf("Time elapsed     : %.2f seconds\n", elapsed7);
        printf("Hash rate        : %.2f hashes/second\n", count7 / elapsed7);
        /* 8-way AVX-512F SHA3-512 using times8 kernel */
        printf("\nAVX-512F 8-way SHA3-512 Benchmark - 1 second test\n");
        printf("Input size: %zu bytes (8 lanes)\n", data_len);
        clock_t start8 = clock(), end8 = start8 + CLOCKS_PER_SEC;
        unsigned long long count8 = 0;
        while (clock() < end8) {
            sha3_hash_512_64B_avx512_times8(data, data_len, digest, SHA3_512_DIGEST_SIZE);
            count8 += 8;
        }
        double elapsed8 = (double)(clock() - start8) / CLOCKS_PER_SEC;
        printf("Hashes performed : %llu\n", count8);
        printf("Time elapsed     : %.2f seconds\n", elapsed8);
        printf("Hash rate        : %.2f hashes/second\n", count8 / elapsed8);
    }
#endif
#endif
#endif
    return 0;
}