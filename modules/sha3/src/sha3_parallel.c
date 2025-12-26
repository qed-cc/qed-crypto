/* SPDX-License-Identifier: Apache-2.0 */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
/* Copyright (c) 2025 Rhett Creighton */
/*
 * @file sha3_parallel.c
 * @brief Parallel SHA3 hashing across multiple threads
 */

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <unistd.h>
#include "sha3.h"
#ifdef __GNUC__
#include "KeccakP-1600-times8-SnP.h"
#endif
// For multi-buffer AVX-512 8-way sponge (disabled due to missing third-party code)
// #ifdef __GNUC__
// #include "KeccakP-1600-times8-SnP.h"
// #endif
// Internal Keccak sponge API (to absorb pre-padded blocks)
extern int keccak_init(uint64_t state[25]);
extern void keccak_absorb(uint64_t *state, const uint8_t *data, size_t len, size_t rate);
extern void keccak_squeeze(uint64_t *state, uint8_t *output, size_t output_len, size_t rate);
// AVX-512×8 Keccak-f[1600] permutation
#ifdef __GNUC__
extern void keccak_permutation8_avx512(uint64_t *s0, uint64_t *s1, uint64_t *s2, uint64_t *s3,
                                       uint64_t *s4, uint64_t *s5, uint64_t *s6, uint64_t *s7);
#endif
/* Declarations for specialized one-shot 64-byte hash functions */
extern int sha3_hash_256_64B_avx512_times8(const void *data, size_t len, void *digest, size_t digest_size);
extern int sha3_hash_256_64B_avx2(const void *data, size_t len, void *digest, size_t digest_size);
extern int sha3_hash_512_64B_avx512_times8(const void *data, size_t len, void *digest, size_t digest_size);
extern int sha3_hash_512_64B_avx2(const void *data, size_t len, void *digest, size_t digest_size);

typedef struct {
    sha3_hash_type type;
    const uint8_t *data;
    uint8_t *output;
    size_t len;          /* input message length */
    size_t digest_size;
    size_t start;
    size_t end;
    int have_avx512;
    int have_avx2;
} sha3_parallel_arg;

static void *sha3_parallel_thread(void *arg) {
    sha3_parallel_arg *a = (sha3_parallel_arg *)arg;
    const uint8_t *data = a->data;
    uint8_t *output = a->output;
    size_t len = a->len;
    size_t digest = a->digest_size;
    size_t start = a->start;
    size_t end = a->end;
    /* Prefetch distance in blocks to hide memory latency (tunable) */
    #define PF_DIST 64
    /* CPU feature flags (inherited from parent) */
    int have_avx512 = a->have_avx512;
    int have_avx2   = a->have_avx2;
    /* 8-way AVX-512 path for pre-padded blocks (len == block size) */
    if (have_avx512 && (a->type == SHA3_256 || a->type == SHA3_512) &&
        ((len == SHA3_256_BLOCK_SIZE && a->type == SHA3_256) ||
         (len == SHA3_512_BLOCK_SIZE && a->type == SHA3_512))) {
        size_t BS = len;
        size_t DIG = digest;
        size_t i = start;
        while (i + 8 <= end) {
            if (i + PF_DIST < end) __builtin_prefetch(data + (i + PF_DIST) * BS, 0, 3);
            uint64_t s0[25] = {0}, s1[25] = {0}, s2[25] = {0}, s3[25] = {0};
            uint64_t s4[25] = {0}, s5[25] = {0}, s6[25] = {0}, s7[25] = {0};
            const uint8_t *base = data + i * BS;
            size_t lanes_per_state = BS / 8;
            for (size_t k = 0; k < lanes_per_state; ++k) {
                s0[k] = ((const uint64_t*)(base + 0*BS))[k];
                s1[k] = ((const uint64_t*)(base + 1*BS))[k];
                s2[k] = ((const uint64_t*)(base + 2*BS))[k];
                s3[k] = ((const uint64_t*)(base + 3*BS))[k];
                s4[k] = ((const uint64_t*)(base + 4*BS))[k];
                s5[k] = ((const uint64_t*)(base + 5*BS))[k];
                s6[k] = ((const uint64_t*)(base + 6*BS))[k];
                s7[k] = ((const uint64_t*)(base + 7*BS))[k];
            }
            keccak_permutation8_avx512(s0, s1, s2, s3, s4, s5, s6, s7);
            for (int lane = 0; lane < 8; ++lane) {
                uint64_t *state = (lane == 0 ? s0 : lane == 1 ? s1 : lane == 2 ? s2 : lane == 3 ? s3 :
                                  lane == 4 ? s4 : lane == 5 ? s5 : lane == 6 ? s6 : s7);
                uint8_t *dst = output + (i + lane) * DIG;
                for (size_t k = 0; k < DIG / 8; ++k) {
                    ((uint64_t*)dst)[k] = state[k];
                }
            }
            i += 8;
        }
        /* leftovers */
        for (; i < end; ++i) {
            const void *msg = data + i * BS;
            void *digp = output + i * DIG;
            sha3_hash(a->type, msg, BS, digp, DIG);
        }
        return NULL;
    }
    /* Fast multi-buffer 8-way path for arbitrary equal-length messages (len < block size) */
    if (have_avx512 && (a->type == SHA3_256 || a->type == SHA3_512)) {
        size_t BS = (a->type == SHA3_256 ? SHA3_256_BLOCK_SIZE : SHA3_512_BLOCK_SIZE);
        if (len > 0 && len < BS) {
            size_t DIG = digest;
            size_t i = start;
            while (i + 8 <= end) {
                KeccakP1600times8_SIMD512_states st;
                KeccakP1600times8_InitializeAll(&st);
                for (unsigned lane = 0; lane < 8; ++lane) {
                    const uint8_t *src = data + (i + lane) * len;
                    KeccakP1600times8_OverwriteBytes(&st, lane, src, 0, (unsigned)len);
                    KeccakP1600times8_OverwriteBytes(&st, lane, (const unsigned char[]){0x06}, (unsigned)len, 1);
                    KeccakP1600times8_OverwriteWithZeroes(&st, lane, (unsigned)(len + 1));
                    KeccakP1600times8_OverwriteBytes(&st, lane, (const unsigned char[]){0x80}, (unsigned)(BS - 1), 1);
                }
                KeccakP1600times8_PermuteAll_24rounds(&st);
                for (unsigned lane = 0; lane < 8; ++lane) {
                    uint8_t *dst = output + (i + lane) * DIG;
                    KeccakP1600times8_ExtractBytes(&st, lane, dst, 0, (unsigned)DIG);
                }
                i += 8;
            }
            for (; i < end; ++i) {
                const uint8_t *src = data + i * len;
                uint8_t *dst = output + i * DIG;
                sha3_hash(a->type, src, len, dst, DIG);
            }
            return NULL;
        }
    }
    /* Fast multi-buffer 8-way path for 64-byte messages with AVX-512 */
    if (have_avx512 && (a->type == SHA3_256 || a->type == SHA3_512) && len == 64) {
        size_t BS = (a->type == SHA3_256 ? SHA3_256_BLOCK_SIZE : SHA3_512_BLOCK_SIZE);
        size_t i = start;
        while (i + 8 <= end) {
            if (i + PF_DIST < end) __builtin_prefetch(data + (i + PF_DIST) * len, 0, 3);
            uint8_t buf0[SHA3_MAX_BLOCK_SIZE], buf1[SHA3_MAX_BLOCK_SIZE], buf2[SHA3_MAX_BLOCK_SIZE], buf3[SHA3_MAX_BLOCK_SIZE];
            uint8_t buf4[SHA3_MAX_BLOCK_SIZE], buf5[SHA3_MAX_BLOCK_SIZE], buf6[SHA3_MAX_BLOCK_SIZE], buf7[SHA3_MAX_BLOCK_SIZE];
            uint64_t s0[25] = {0}, s1[25] = {0}, s2[25] = {0}, s3[25] = {0};
            uint64_t s4[25] = {0}, s5[25] = {0}, s6[25] = {0}, s7[25] = {0};
            const uint8_t *src = data + i * len;
            uint8_t *bufs[8] = {buf0, buf1, buf2, buf3, buf4, buf5, buf6, buf7};
            for (int j = 0; j < 8; ++j) {
                uint8_t *b = bufs[j];
                memcpy(b, src + j * len, len);
                b[len] = 0x06;
                memset(b + len + 1, 0, BS - (len + 1));
                b[BS - 1] ^= 0x80;
            }
            const uint64_t *lanes0 = (const uint64_t *)buf0;
            const uint64_t *lanes1 = (const uint64_t *)buf1;
            const uint64_t *lanes2 = (const uint64_t *)buf2;
            const uint64_t *lanes3 = (const uint64_t *)buf3;
            const uint64_t *lanes4 = (const uint64_t *)buf4;
            const uint64_t *lanes5 = (const uint64_t *)buf5;
            const uint64_t *lanes6 = (const uint64_t *)buf6;
            const uint64_t *lanes7 = (const uint64_t *)buf7;
            for (int k = 0; k < (int)(BS / 8); ++k) {
                s0[k] = lanes0[k]; s1[k] = lanes1[k]; s2[k] = lanes2[k]; s3[k] = lanes3[k];
                s4[k] = lanes4[k]; s5[k] = lanes5[k]; s6[k] = lanes6[k]; s7[k] = lanes7[k];
            }
            keccak_permutation8_avx512(s0, s1, s2, s3, s4, s5, s6, s7);
            uint8_t *dst = output + i * digest;
            uint64_t *out0 = (uint64_t *)(dst + 0 * digest);
            uint64_t *out1 = (uint64_t *)(dst + 1 * digest);
            uint64_t *out2 = (uint64_t *)(dst + 2 * digest);
            uint64_t *out3 = (uint64_t *)(dst + 3 * digest);
            uint64_t *out4 = (uint64_t *)(dst + 4 * digest);
            uint64_t *out5 = (uint64_t *)(dst + 5 * digest);
            uint64_t *out6 = (uint64_t *)(dst + 6 * digest);
            uint64_t *out7 = (uint64_t *)(dst + 7 * digest);
            for (int k = 0; k < (int)(digest / 8); ++k) {
                out0[k] = s0[k]; out1[k] = s1[k]; out2[k] = s2[k]; out3[k] = s3[k];
                out4[k] = s4[k]; out5[k] = s5[k]; out6[k] = s6[k]; out7[k] = s7[k];
            }
            i += 8;
        }
        for (; i < end; ++i) {
            const void *msg = data + i * len;
            void *dig = output + i * digest;
            sha3_hash(a->type, msg, len, dig, digest);
        }
        return NULL;
    }
    /* Fast multi-buffer 4-way path for 64-byte messages with AVX2 */
    if (have_avx2 && (a->type == SHA3_256 || a->type == SHA3_512) && len == 64) {
#ifdef __GNUC__
        size_t BS = (a->type == SHA3_256 ? SHA3_256_BLOCK_SIZE : SHA3_512_BLOCK_SIZE);
        size_t i = start;
        while (i + 4 <= end) {
            /* Prefetch block PF_DIST ahead */
            if (i + PF_DIST < end) __builtin_prefetch(data + (i + PF_DIST) * len, 0, 3);
            uint8_t buf0[SHA3_MAX_BLOCK_SIZE];
            uint8_t buf1[SHA3_MAX_BLOCK_SIZE];
            uint8_t buf2[SHA3_MAX_BLOCK_SIZE];
            uint8_t buf3[SHA3_MAX_BLOCK_SIZE];
            uint64_t s0[25] = {0}, s1[25] = {0}, s2[25] = {0}, s3[25] = {0};
            /* pad and load each buffer */
            uint8_t *bs[4] = {buf0, buf1, buf2, buf3};
            for (int j = 0; j < 4; ++j) {
                uint8_t *b = bs[j];
                memcpy(b, data + (i+j)*len, len);
                b[len] = 0x06;
                memset(b + len + 1, 0, BS - (len + 1));
                b[BS - 1] ^= 0x80;
            }
            /* map lanes to state words */
            const uint64_t *lanes0 = (const uint64_t *)buf0;
            const uint64_t *lanes1 = (const uint64_t *)buf1;
            const uint64_t *lanes2 = (const uint64_t *)buf2;
            const uint64_t *lanes3 = (const uint64_t *)buf3;
            for (int k = 0; k < (int)(BS/8); ++k) {
                s0[k] = lanes0[k];
                s1[k] = lanes1[k];
                s2[k] = lanes2[k];
                s3[k] = lanes3[k];
            }
            extern void keccak_permutation4_avx2(uint64_t *, uint64_t *, uint64_t *, uint64_t *);
            keccak_permutation4_avx2(s0, s1, s2, s3);
            /* extract digests */
            uint64_t *o0 = (uint64_t *)(output + (i+0)*digest);
            uint64_t *o1 = (uint64_t *)(output + (i+1)*digest);
            uint64_t *o2 = (uint64_t *)(output + (i+2)*digest);
            uint64_t *o3 = (uint64_t *)(output + (i+3)*digest);
            for (int k = 0; k < (int)(digest/8); ++k) {
                o0[k] = s0[k];
                o1[k] = s1[k];
                o2[k] = s2[k];
                o3[k] = s3[k];
            }
            i += 4;
        }
        /* leftover */
        for (size_t i = start + ((end - start)/4)*4; i < end; ++i) {
            const void *msg = data + i*len;
            void *dig = output + i*digest;
            sha3_hash(a->type, msg, len, dig, digest);
        }
        return NULL;
#endif
    }
    /* Generic per-message path */
    for (size_t i = start; i < end; ++i) {
        /* Prefetch PF_DIST blocks ahead */
        if (i + PF_DIST < end) __builtin_prefetch(data + (i + PF_DIST) * len, 0, 3);
        const void *msg = data + i*len;
        void *dig = output + i*digest;
        sha3_hash(a->type, msg, len, dig, digest);
    }
    return NULL;
}

int sha3_hash_parallel_len(sha3_hash_type type,
                           const void *data,
                           size_t len,
                           void *output,
                           size_t n) {
    if (!data || !output) return -1;
    if (n == 0) return 0;
    size_t digest_size = sha3_get_digest_size(type);
    if (digest_size == 0) return -1;
    /* Confirm len is not above block size */
    size_t BS = sha3_get_block_size(type);
    if (BS == 0 || len > BS) return -1;
    /* Detect CPU features once */
    int have_avx512 = 0, have_avx2 = 0;
#ifdef __GNUC__
    have_avx512 = __builtin_cpu_supports("avx512f");
    have_avx2   = __builtin_cpu_supports("avx2");
#endif
    /* Determine number of threads */
    long nproc = sysconf(_SC_NPROCESSORS_ONLN);
    int nthreads = (nproc > 0 ? (int)nproc : 1);
    if ((size_t)nthreads > n) nthreads = (int)n;

    /* No separate padding: sha3_parallel_thread handles padding per-message */
    const uint8_t *data_ptr = (const uint8_t *)data;
    size_t len_for_thread = len;

    pthread_t *threads = malloc(sizeof(pthread_t) * nthreads);
    if (!threads) return -1;
    sha3_parallel_arg *args = malloc(sizeof(sha3_parallel_arg) * nthreads);
    if (!args) {
        free(threads);
        return -1;
    }

    /* Partition work across threads */
    size_t base = n / nthreads;
    size_t rem = n % nthreads;
    size_t offset = 0;
    for (int t = 0; t < nthreads; ++t) {
        size_t count = base + (t < (int)rem ? 1 : 0);
        args[t].type        = type;
        args[t].have_avx512 = have_avx512;
        args[t].have_avx2   = have_avx2;
        args[t].data        = data_ptr;
        args[t].output      = (uint8_t *)output;
        args[t].len         = len_for_thread;
        args[t].digest_size = digest_size;
        args[t].start       = offset;
        args[t].end         = offset + count;
        offset += count;
        pthread_attr_t attr;
        cpu_set_t cpuset;
        pthread_attr_init(&attr);
        CPU_ZERO(&cpuset);
        CPU_SET(t, &cpuset);
        pthread_attr_setaffinity_np(&attr, sizeof(cpuset), &cpuset);
        if (pthread_create(&threads[t], &attr, sha3_parallel_thread, &args[t]) != 0) {
            pthread_attr_destroy(&attr);
            for (int j = 0; j < t; ++j) pthread_join(threads[j], NULL);
            free(args);
            free(threads);
            return -1;
        }
        pthread_attr_destroy(&attr);
    }

    /* Join threads */
    for (int t = 0; t < nthreads; ++t) {
        pthread_join(threads[t], NULL);
    }
    free(args);
    free(threads);
    return 0;
}

/**
 * @brief Parallel hash for equal-length messages with auto-padding.
 */
int sha3_hash_parallel_eqlen(sha3_hash_type type,
                             const void *data,
                             size_t msg_len,
                             void *output,
                             size_t n) {
    if (!data || !output) return -1;
    if (n == 0) return 0;
    size_t BS = sha3_get_block_size(type);
    if (msg_len > BS) return -1;
    /* If already block-sized, dispatch directly */
    if (msg_len == BS) {
        return sha3_hash_parallel_len(type, data, BS, output, n);
    }
    /* Pad all messages into a contiguous BS-byte buffer */
    uint8_t *padded;
    if (posix_memalign((void **)&padded, 64, n * BS) != 0) {
        return -1;
    }
    for (size_t i = 0; i < n; i++) {
        uint8_t *dst = padded + i * BS;
        const uint8_t *src = (const uint8_t *)data + i * msg_len;
        memcpy(dst, src, msg_len);
        dst[msg_len] = 0x06;
        memset(dst + msg_len + 1, 0, BS - (msg_len + 1));
        dst[BS - 1] ^= 0x80;
    }
    int rc = sha3_hash_parallel_len(type, padded, BS, output, n);
    free(padded);
    return rc;
}
/**
 * @brief Compute multiple SHA3 hashes in parallel for fixed-length (64-byte) messages.
 *
 * Simple wrapper around sha3_hash_parallel_len using len=64 to leverage
 * 8-way AVX-512F or 4-way AVX2 multi-buffer kernels on SHA3_256/SHA3_512.
 */
int sha3_hash_parallel(sha3_hash_type type,
                       const void *data,
                       void *output,
                       size_t n) {
    return sha3_hash_parallel_len(type, data, 64, output, n);
}

/* Helper struct and thread entry for sha3_hash_parallel_same */
typedef struct {
    sha3_hash_type type;
    const uint8_t *msg;
    uint8_t *output;
    size_t len;
    size_t digest_size;
    size_t start;
    size_t end;
} sha3_parallel_same_arg;

static void *sha3_parallel_same_thread(void *arg) {
    sha3_parallel_same_arg *a = arg;
    sha3_hash_type type = a->type;
    const void *msg = a->msg;
    size_t len = a->len;
    size_t ds = a->digest_size;
    uint8_t *out = a->output;
#ifdef __GNUC__
    int have_avx512 = __builtin_cpu_supports("avx512f");
    int have_avx2   = __builtin_cpu_supports("avx2");
#else
    int have_avx512 = 0, have_avx2 = 0;
#endif
    for (size_t i = a->start; i < a->end; ++i) {
        void *dig = out + i * ds;
        if (have_avx512 && type == SHA3_256 && len == 64 && ds >= SHA3_256_DIGEST_SIZE) {
            sha3_hash_256_64B_avx512_times8(msg, len, dig, ds);
        } else if (have_avx2 && type == SHA3_256 && len == 64 && ds >= SHA3_256_DIGEST_SIZE) {
            sha3_hash_256_64B_avx2(msg, len, dig, ds);
        } else if (have_avx512 && type == SHA3_512 && len == 64 && ds >= SHA3_512_DIGEST_SIZE) {
            sha3_hash_512_64B_avx512_times8(msg, len, dig, ds);
        } else if (have_avx2 && type == SHA3_512 && len == 64 && ds >= SHA3_512_DIGEST_SIZE) {
            sha3_hash_512_64B_avx2(msg, len, dig, ds);
        } else {
            sha3_hash(type, msg, len, dig, ds);
        }
    }
    return NULL;
}

int sha3_hash_parallel_same(sha3_hash_type type,
                            const void *msg,
                            size_t len,
                            void *output,
                            size_t n) {
    if (!msg || !output) return -1;
    if (n == 0) return 0;
    size_t ds = sha3_get_digest_size(type);
    if (ds == 0) return -1;
    long nproc = sysconf(_SC_NPROCESSORS_ONLN);
    int nthreads = (nproc > 0 ? (int)nproc : 1);
    if ((size_t)nthreads > n) nthreads = (int)n;

    pthread_t *threads = malloc(sizeof(pthread_t) * nthreads);
    if (!threads) return -1;
    sha3_parallel_same_arg *args = malloc(sizeof(sha3_parallel_same_arg) * nthreads);
    if (!args) { free(threads); return -1; }

    size_t base = n / nthreads;
    size_t rem = n % nthreads;
    size_t offset = 0;
    for (int t = 0; t < nthreads; ++t) {
        size_t count = base + (t < (int)rem ? 1 : 0);
        args[t].type = type;
        args[t].msg = (const uint8_t *)msg;
        args[t].output = (uint8_t *)output;
        args[t].len = len;
        args[t].digest_size = ds;
        args[t].start = offset;
        args[t].end = offset + count;
        offset += count;
        pthread_create(&threads[t], NULL, sha3_parallel_same_thread, &args[t]);
    }
    for (int t = 0; t < nthreads; ++t) pthread_join(threads[t], NULL);
    free(args);
    free(threads);
    return 0;
}