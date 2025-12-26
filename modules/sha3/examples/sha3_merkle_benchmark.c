/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/*
 * sha3_merkle_benchmark.c
 *
 * Example: benchmark 4-ary Merkle tree build using SHA3-256
 */
#define _POSIX_C_SOURCE 200809L  /* for posix_memalign & clock_gettime */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include "sha3.h"

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
    size_t num_leaves = 1000000;
    if (argc > 1) num_leaves = strtoull(argv[1], NULL, 0);
    printf("Building 4-ary Merkle tree with %zu leaves...\n", num_leaves);

    /* Allocate and fill leaves */
    size_t leaf_size = SHA3_256_DIGEST_SIZE;
    uint8_t *leaves;
    if (posix_memalign((void**)&leaves, 64, num_leaves * leaf_size) != 0) {
        perror("posix_memalign");
        return 1;
    }
    {
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        uint64_t seed = ((uint64_t)ts.tv_sec << 32) ^ ts.tv_nsec ^ (uint64_t)getpid();
        uint64_t *p = (uint64_t*)leaves;
        size_t count = num_leaves * (leaf_size / sizeof(uint64_t));
        for (size_t i = 0; i < count; i++) {
            seed = seed * 6364136223846793005ULL + 1;
            p[i] = seed;
        }
    }
    uint8_t root[leaf_size];
    double t0 = now_sec();
    if (sha3_merkle_tree4_32(leaves, num_leaves, root) != 0) {
        fprintf(stderr, "sha3_merkle_tree4_32 failed\n");
        free(leaves);
        return 1;
    }
    double t1 = now_sec();

    double elapsed = t1 - t0;
    double mhs = (num_leaves - 1) / (elapsed * 1e6);
    printf("Built in %.6f s -> %.2f M hashes/s\n", elapsed, mhs);
    printf("Root: ");
    for (size_t i = 0; i < leaf_size; i++) printf("%02x", root[i]);
    printf("\n");

    free(leaves);
    return 0;
}