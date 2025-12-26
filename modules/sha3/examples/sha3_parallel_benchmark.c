/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */

/*
 * @file sha3_parallel_benchmark.c
 * @brief Benchmark parallel SHA3 hashing over multiple threads
 * Requires POSIX.1b clock_gettime and pthreads
 */
#define _POSIX_C_SOURCE 200112L  /* for posix_memalign */
#include "sha3.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
#include <string.h>  /* memcpy, memset */

int main(int argc, char *argv[]) {
    int nproc = sysconf(_SC_NPROCESSORS_ONLN);
    if (nproc < 1) nproc = 1;
    /* Number of messages per thread; total messages = per_thread * nproc */
    size_t per_thread = 500000;
    size_t n = per_thread * nproc;
    if (argc > 1) {
        n = strtoull(argv[1], NULL, 0);
    }
    /* Message length in bytes (default 64, or supply as second arg) */
    size_t len = 64;
    if (argc > 2) {
        len = strtoull(argv[2], NULL, 0);
    }
    size_t digest = sha3_get_digest_size(SHA3_256);
    uint8_t *in = NULL;
    uint8_t *out = NULL;
    /* 64-byte alignment for optimal vector loads */
    if (posix_memalign((void**)&in, 64, n * len) != 0) {
        fprintf(stderr, "Allocation failure for input buffer\n");
        return 1;
    }
    if (posix_memalign((void**)&out, 64, n * digest) != 0) {
        free(in);
        fprintf(stderr, "Allocation failure for output buffer\n");
        return 1;
    }
    /* initialize raw input with repeating pattern */
    for (size_t i = 0; i < n * len; ++i) {
        in[i] = (uint8_t)(i & 0xFF);
    }
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    /* Parallel hash of n messages of length len (padding done internally) */
    if (sha3_hash_parallel_len(SHA3_256, in, len, out, n) != 0) {
        fprintf(stderr, "sha3_hash_parallel_len failed\n");
        free(in);
        free(out);
        return 1;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    double msgs_per_sec = n / elapsed;
    double mb_per_sec = msgs_per_sec * len / (1024.0 * 1024.0);
    printf("sha3_hash_parallel_len: %zu messages of %zu bytes in %.3f s\n", n, len, elapsed);
    printf("Throughput: %.0f msgs/s (%.1f MiB/s) on %d threads\n", msgs_per_sec, mb_per_sec, nproc);
    free(in);
    free(out);
    return 0;
}