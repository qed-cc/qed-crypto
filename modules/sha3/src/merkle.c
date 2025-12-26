/* SPDX-License-Identifier: Apache-2.0 */
/*
 * @file merkle.c
 * @brief 4-ary Merkle tree construction using fixed 32-byte leaves and SHA3-256.
 *
 * This implementation uses a persistent pool of worker threads to hash each level
 * with AVX-512×8 multi-buffer Keccak. Packing and SHA3 padding are done in-worker
 * to parallelize the entire build.
 */
#define _POSIX_C_SOURCE 200112L
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#ifdef __GNUC__
#include "KeccakP-1600-times8-SnP.h"
#endif
#include "sha3.h"

// Context for the Merkle tree build
typedef struct {
    size_t rate;        // SHA3-256 rate (136 bytes)
    size_t leaf_size;   // Leaf/digest size (32 bytes)
    size_t branch;      // Number of children per node (4)
    const uint8_t *cur; // Current level input
    uint8_t *buf1, *buf2; // Ping-pong buffers
    uint8_t *next;      // Output buffer for this level
    size_t parents;     // Nodes at this level
    int nthreads;       // Number of worker threads
    int done;           // Terminate flag
    pthread_barrier_t barrier; // Two-phase sync barrier
} merkle_ctx_t;

// Argument for worker threads
typedef struct {
    merkle_ctx_t *ctx;
    int tid;
} worker_arg_t;

// Worker: waits for pack signal, then packs/pads+hashes in spans of 8, syncs
static void *merkle_worker(void *arg) {
    worker_arg_t *a = arg;
    merkle_ctx_t *c = a->ctx;
    for (;;) {
        pthread_barrier_wait(&c->barrier);
        if (c->done) break;
        size_t P = c->parents;
        size_t R = c->rate;
        size_t D = c->leaf_size;
        const uint8_t *input = c->cur;
        uint8_t *output = c->next;
        // AVX-512×8 multi-buffer
        for (size_t i = (size_t)a->tid * 8; i + 8 <= P; i += c->nthreads * 8) {
            KeccakP1600times8_SIMD512_states st;
            KeccakP1600times8_InitializeAll(&st);
            for (int lane = 0; lane < 8; lane++) {
                const uint8_t *leaf = input + (i + lane) * D;
                // absorb leaf
                KeccakP1600times8_OverwriteBytes(&st, lane, leaf, 0, (unsigned)D);
                // pad
                KeccakP1600times8_OverwriteBytes(&st, lane, (uint8_t[]){0x06}, (unsigned)D, 1);
                KeccakP1600times8_OverwriteWithZeroes(&st, lane, (unsigned)(D + 1));
                KeccakP1600times8_OverwriteBytes(&st, lane, (uint8_t[]){0x80}, (unsigned)(R - 1), 1);
            }
            KeccakP1600times8_PermuteAll_24rounds(&st);
            for (int lane = 0; lane < 8; lane++) {
                KeccakP1600times8_ExtractBytes(&st, lane,
                    output + (i + lane) * D, 0, (unsigned)D);
            }
        }
        // Scalar fallback for remainder
        size_t start = (P / 8) * 8;
        uint8_t tmp[200];
        for (size_t i = start; i < P; i++) {
            const uint8_t *leaf = input + i * D;
            memcpy(tmp, leaf, D);
            tmp[D] = 0x06;
            memset(tmp + D + 1, 0, R - D - 1);
            tmp[R - 1] ^= 0x80;
            sha3_hash(SHA3_256, tmp, R, output + i * D, D);
        }
        pthread_barrier_wait(&c->barrier);
    }
    return NULL;
}

// API: 32-byte 4-ary Merkle tree using SHA3-256
int sha3_merkle_tree4_32(const uint8_t *leaves, size_t num_leaves, uint8_t *root) {
    if (!leaves || !root || num_leaves == 0) return -1;
    merkle_ctx_t ctx;
    ctx.leaf_size = SHA3_256_DIGEST_SIZE;
    ctx.rate      = sha3_get_block_size(SHA3_256);
    ctx.branch    = ctx.rate / ctx.leaf_size;
    ctx.done      = 0;
    ctx.nthreads  = (int)(sysconf(_SC_NPROCESSORS_ONLN) > 0 ?
                       sysconf(_SC_NPROCESSORS_ONLN) : 1);
    pthread_barrier_init(&ctx.barrier, NULL, ctx.nthreads + 1);
    size_t maxp = (num_leaves + ctx.branch - 1) / ctx.branch;
    uint8_t *bufA, *bufB;
    if (posix_memalign((void**)&bufA, 64, maxp * ctx.leaf_size) != 0 ||
        posix_memalign((void**)&bufB, 64, maxp * ctx.leaf_size) != 0) {
        free(bufA); free(bufB);
        return -1;
    }
    ctx.buf1 = bufA;
    ctx.buf2 = bufB;
    ctx.next = ctx.buf1;
    pthread_t threads[ctx.nthreads];
    worker_arg_t args[ctx.nthreads];
    for (int t = 0; t < ctx.nthreads; t++) {
        args[t].ctx = &ctx;
        args[t].tid = t;
        pthread_create(&threads[t], NULL, merkle_worker, &args[t]);
    }
    const uint8_t *cur = leaves;
    uint8_t *swap_buf = ctx.buf2;
    size_t N = num_leaves;
    while (N > 1) {
        ctx.parents = (N + ctx.branch - 1) / ctx.branch;
        ctx.cur     = cur;
        pthread_barrier_wait(&ctx.barrier);
        pthread_barrier_wait(&ctx.barrier);
        N   = ctx.parents;
        cur = ctx.next;
        ctx.next = swap_buf;
        swap_buf = (uint8_t*)cur;
    }
    memcpy(root, cur, ctx.leaf_size);
    ctx.done = 1;
    pthread_barrier_wait(&ctx.barrier);
    for (int t = 0; t < ctx.nthreads; t++) pthread_join(threads[t], NULL);
    pthread_barrier_destroy(&ctx.barrier);
    free(bufA); free(bufB);
    return 0;
}