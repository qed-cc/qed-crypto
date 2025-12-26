/*
 * bench_mul.c
 * Benchmark GF(2^128) multiplication implementations.
 * For each method, run a warm-up phase to estimate timing, then adjust iterations
 * so that measurement takes approximately 1 second, and report ops/sec.
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h> // for _mm_prefetch
#include <pthread.h>    // for multi-threaded benchmarking
#include <time.h>       // for clock_gettime
#include "gf128.h"

// Number of random element pairs
#define N_PAIRS 1024

static gf128_t a_rand[N_PAIRS], b_rand[N_PAIRS];
// CSV output mode (enabled with --csv)
static int csv_mode = 0;

// Benchmark a GF128 multiplication function with random inputs
static void bench(const char *name, gf128_t (*mul)(gf128_t, gf128_t)) {
    const double target_sec = 1.0;
    const long warmup_iters = 10000;
    volatile gf128_t r;
    clock_t t0, t1;
    double warmup_sec, measure_sec, ops_per_sec;
    long iters;

    // Warm-up phase (use pointer wrap-around instead of modulo)
    t0 = clock();
    size_t widx = 0;
    for (long i = 0; i < warmup_iters; i++) {
        r = mul(a_rand[widx], b_rand[widx]);
        if (++widx == N_PAIRS) widx = 0;
    }
    t1 = clock();
    warmup_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    if (warmup_sec <= 0.0) warmup_sec = 1.0 / CLOCKS_PER_SEC;

    // Determine iterations for ~1 second run
    iters = (long)(warmup_iters * (target_sec / warmup_sec));
    if (iters < 1) iters = 1;

    // Measured run (pointer wrap-around + prefetch)
    t0 = clock();
    size_t midx = 0;
    for (long i = 0; i < iters; i++) {
        // Prefetch next pair
        size_t pidx = (midx + 1 == N_PAIRS) ? 0 : midx + 1;
        _mm_prefetch((const char*)&a_rand[pidx], _MM_HINT_T0);
        _mm_prefetch((const char*)&b_rand[pidx], _MM_HINT_T0);
        r = mul(a_rand[midx], b_rand[midx]);
        if (++midx == N_PAIRS) midx = 0;
    }
    t1 = clock();
    measure_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    ops_per_sec = iters / measure_sec;

    // Report in million operations per second
    if (csv_mode) {
        printf("%s,%.2f\n", name, ops_per_sec / 1e6);
    } else {
        printf("%-16s: %8.2f Mops/sec\n", name, ops_per_sec / 1e6);
    }
    (void)r;
}

// Benchmark a 2-way batched GF128 multiply
static void bench2(const char *name, void (*mul2)(const gf128_t a[2], const gf128_t b[2], gf128_t out[2])) {
    const double target_sec = 1.0;
    const long warmup_iters = 10000;
    volatile gf128_t out2[2];
    clock_t t0, t1;
    double warmup_sec, measure_sec, ops_per_sec;
    long iters;

    // Warm-up phase (pointer wrap-around)
    t0 = clock();
    size_t widx2 = 0;
    for (long i = 0; i < warmup_iters; i++) {
        // widx2 always even; uses two contiguous elements
        mul2(&a_rand[widx2], &b_rand[widx2], out2);
        widx2 += 2;
        if (widx2 == N_PAIRS) widx2 = 0;
    }
    t1 = clock();
    warmup_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    if (warmup_sec <= 0.0) warmup_sec = 1.0 / CLOCKS_PER_SEC;

    // Determine iters for ~1s
    iters = (long)(warmup_iters * (target_sec / warmup_sec));
    if (iters < 1) iters = 1;

    // Measured run (pointer wrap-around + prefetch)
    t0 = clock();
    size_t midx2 = 0;
    for (long i = 0; i < iters; i++) {
        size_t pidx2 = (midx2 + 2 >= N_PAIRS) ? 0 : midx2 + 2;
        _mm_prefetch((const char*)&a_rand[pidx2], _MM_HINT_T0);
        _mm_prefetch((const char*)&b_rand[pidx2], _MM_HINT_T0);
        mul2(&a_rand[midx2], &b_rand[midx2], out2);
        midx2 += 2;
        if (midx2 == N_PAIRS) midx2 = 0;
    }
    t1 = clock();
    measure_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    ops_per_sec = (2.0 * iters) / measure_sec;

    // Report
    if (csv_mode) {
        printf("%s,%.2f\n", name, ops_per_sec / 1e6);
    } else {
        printf("%-16s: %8.2f Mops/sec\n", name, ops_per_sec / 1e6);
    }
}

// Benchmark a 4-way batched GF128 multiply
static void bench4(const char *name, void (*mul4)(const gf128_t a[4], const gf128_t b[4], gf128_t out[4])) {
    const double target_sec = 1.0;
    const long warmup_iters = 10000;
    volatile gf128_t out4[4];
    // Accumulator to prevent dead-code elimination of mul4
    volatile uint64_t acc4 = 0;
    clock_t t0, t1;
    double warmup_sec, measure_sec, ops_per_sec;
    long iters;

    // Warm-up phase (pointer wrap-around)
    t0 = clock();
    size_t widx4 = 0;
    for (long i = 0; i < warmup_iters; i++) {
        mul4(&a_rand[widx4], &b_rand[widx4], out4);
        widx4 += 4;
        if (widx4 >= N_PAIRS) widx4 = 0;
    }
    t1 = clock();
    warmup_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    if (warmup_sec <= 0.0) warmup_sec = 1.0 / CLOCKS_PER_SEC;

    // Determine iterations for ~1 second run
    iters = (long)(warmup_iters * (target_sec / warmup_sec));
    if (iters < 1) iters = 1;

    // Measured run (pointer wrap-around + prefetch)
    t0 = clock();
    size_t midx4 = 0;
    for (long i = 0; i < iters; i++) {
        size_t pidx4 = (midx4 + 4 >= N_PAIRS) ? 0 : midx4 + 4;
        _mm_prefetch((const char*)&a_rand[pidx4], _MM_HINT_T0);
        _mm_prefetch((const char*)&b_rand[pidx4], _MM_HINT_T0);
        mul4(&a_rand[midx4], &b_rand[midx4], out4);
        // use result to prevent optimization
        acc4 ^= out4[0].lo;
        midx4 += 4;
        if (midx4 >= N_PAIRS) midx4 = 0;
    }
    t1 = clock();
    measure_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    ops_per_sec = (4.0 * iters) / measure_sec;

    // Report
    if (csv_mode) {
        printf("%s,%.2f\n", name, ops_per_sec / 1e6);
    } else {
        printf("%-16s: %8.2f Mops/sec\n", name, ops_per_sec / 1e6);
    }
    (void)acc4;
}
// Benchmark an 8-way batched GF128 multiply
static void bench8(const char *name, void (*mul8)(const gf128_t a[8], const gf128_t b[8], gf128_t out[8])) {
    const double target_sec = 1.0;
    const long warmup_iters = 10000;
    volatile gf128_t out8[8];
    volatile uint64_t acc8 = 0;
    clock_t t0, t1;
    double warmup_sec, measure_sec, ops_per_sec;
    long iters;

    // Warm-up phase
    t0 = clock();
    size_t widx8 = 0;
    for (long i = 0; i < warmup_iters; i++) {
        mul8(&a_rand[widx8], &b_rand[widx8], out8);
        widx8 += 8;
        if (widx8 >= N_PAIRS) widx8 = 0;
    }
    t1 = clock();
    warmup_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    if (warmup_sec <= 0.0) warmup_sec = 1.0 / CLOCKS_PER_SEC;

    // Determine iterations
    iters = (long)(warmup_iters * (target_sec / warmup_sec));
    if (iters < 1) iters = 1;

    // Measured run
    t0 = clock();
    size_t midx8 = 0;
    for (long i = 0; i < iters; i++) {
        size_t pidx8 = (midx8 + 8 >= N_PAIRS) ? 0 : midx8 + 8;
        _mm_prefetch((const char*)&a_rand[pidx8], _MM_HINT_T0);
        _mm_prefetch((const char*)&b_rand[pidx8], _MM_HINT_T0);
        mul8(&a_rand[midx8], &b_rand[midx8], out8);
        acc8 ^= out8[0].lo ^ out8[7].lo;
        midx8 += 8;
        if (midx8 >= N_PAIRS) midx8 = 0;
    }
    t1 = clock();
    measure_sec = (double)(t1 - t0) / CLOCKS_PER_SEC;
    ops_per_sec = (8.0 * iters) / measure_sec;

    // Report
    if (csv_mode) {
        printf("%s,%.2f\n", name, ops_per_sec / 1e6);
    } else {
        printf("%-16s: %8.2f Mops/sec\n", name, ops_per_sec / 1e6);
    }
    (void)acc8;
}
// Multi-threaded 8-way batched benchmark
// Thread function for 8-way bench
struct bench8_mt_arg { void (*mul8)(const gf128_t a[8], const gf128_t b[8], gf128_t out[8]); size_t iters; size_t start_idx; };
static void *bench8_thread_func(void *v) {
    struct bench8_mt_arg *arg = (struct bench8_mt_arg*)v;
    volatile gf128_t out8[8];
    size_t midx = arg->start_idx;
    for (size_t i = 0; i < arg->iters; i++) {
        arg->mul8(&a_rand[midx], &b_rand[midx], out8);
        midx += 8;
        if (midx >= N_PAIRS) midx -= N_PAIRS;
    }
    return NULL;
}
// Spawn threads to run 8-way benchmark in parallel
static void bench8_mt(const char *name, void (*mul8)(const gf128_t a[8], const gf128_t b[8], gf128_t out[8]), int threads) {
    const double target_sec = 1.0;
    const long warmup_iters = 10000;
    double warmup_sec, measure_sec, ops_per_sec;
    long iters;
    struct timespec t0, t1;
    // Warm-up single-thread wall-clock
    clock_gettime(CLOCK_MONOTONIC, &t0);
    size_t widx = 0;
    volatile gf128_t tmp[8];
    for (long i = 0; i < warmup_iters; i++) {
        mul8(&a_rand[widx], &b_rand[widx], tmp);
        widx += 8;
        if (widx >= N_PAIRS) widx = 0;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    warmup_sec = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    if (warmup_sec <= 0.0) warmup_sec = 1e-9;
    iters = (long)(warmup_iters * (target_sec / warmup_sec));
    if (iters < 1) iters = 1;
    // Run in parallel threads
    pthread_t th[threads];
    struct bench8_mt_arg args[threads];
    for (int i = 0; i < threads; i++) {
        args[i].mul8 = mul8;
        args[i].iters = iters;
        args[i].start_idx = (size_t)i * 8 % N_PAIRS;
    }
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < threads; i++) pthread_create(&th[i], NULL, bench8_thread_func, &args[i]);
    for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    measure_sec = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    ops_per_sec = (threads * 8.0 * iters) / measure_sec;
    // Report
    if (csv_mode) {
        printf("%s,%.2f\n", name, ops_per_sec / 1e6);
    } else {
        printf("%-16s: %8.2f Mops/sec\n", name, ops_per_sec / 1e6);
    }
}

int main(int argc, char *argv[]) {
    // Parse command-line flags: --csv and --threads N
    int threads = 1;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--csv") == 0) {
            csv_mode = 1;
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            threads = atoi(argv[++i]);
            if (threads < 1) threads = 1;
        }
    }
    // Seed random number generator
    srand((unsigned)time(NULL));
    // Generate random input pairs
    for (size_t i = 0; i < N_PAIRS; i++) {
        uint64_t hi = ((uint64_t)rand() << 32) | (uint64_t)rand();
        uint64_t lo = ((uint64_t)rand() << 32) | (uint64_t)rand();
        a_rand[i].hi = hi;
        a_rand[i].lo = lo;
        hi = ((uint64_t)rand() << 32) | (uint64_t)rand();
        lo = ((uint64_t)rand() << 32) | (uint64_t)rand();
        b_rand[i].hi = hi;
        b_rand[i].lo = lo;
    }

    if (csv_mode) printf("method,Mops\n");
    // Baseline benchmarks (fallback implementations)
    bench("gf128_mul_base",    gf128_mul_base);
    bench("gf128_mul_table",   gf128_mul_table);
    // Direct PCLMUL (intrinsic path)
    bench("gf128_mul_pclmul",  gf128_mul_pclmul);
#ifdef USE_PCLMUL_KARATSUBA
    // Karatsuba-optimized PCLMUL
    bench("gf128_mul_pclmul_kara", gf128_mul_pclmul_kara);
#endif
    // AVX2 2-way PCLMUL
#ifdef USE_AVX2
    bench2("gf128_mul2_pclmul_avx2", gf128_mul2_pclmul_avx2);
    bench("gf128_mul_pclmul_avx2",  gf128_mul_pclmul_avx2);
#endif
    // AVX-512 4-way PCLMUL
    #ifdef USE_AVX512
    // Super-batched 8-way AVX-512 PCLMUL
    if (threads > 1) {
        bench8_mt("gf128_mul8_pclmul_avx512_super", gf128_mul8_pclmul_avx512_super, threads);
    } else {
        bench8("gf128_mul8_pclmul_avx512_super", gf128_mul8_pclmul_avx512_super);
    }
    // Standard 4-way AVX-512 PCLMUL
    bench4("gf128_mul4_pclmul_avx512",      gf128_mul4_pclmul_avx512);
    bench("gf128_mul_pclmul_avx512",        gf128_mul_pclmul_avx512);
    #ifdef USE_GFNI_MUL
    // Experimental GFNI-only multiply
    bench("gf128_mul_gfni",                 gf128_mul_gfni);
    #endif
    #endif
    // Generic dispatch (table or PCLMUL/Karatsuba)
    bench("gf128_mul",          gf128_mul);
    return 0;
}