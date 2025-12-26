#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <inttypes.h>
#include "gf128.h"

#define BENCH_ITER (1<<18)  // 262144 multiplications

static void bench_variant(const char *name,
                          gf128_t (*fn)(gf128_t, gf128_t),
                          const gf128_t *a,
                          const gf128_t *b,
                          gf128_t *out,
                          size_t n) {
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (size_t i = 0; i < n; i++) {
        out[i] = fn(a[i], b[i]);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    uint64_t ns = (uint64_t)(t1.tv_sec - t0.tv_sec) * 1000000000ULL
                  + (uint64_t)(t1.tv_nsec - t0.tv_nsec);
    double ms_total = ns * 1e-6;
    double ns_avg = (double)ns / n;
    printf("%s: total %.3f ms, avg %.3f ns/mul\n", name, ms_total, ns_avg);
}

int main(void) {
    size_t n = BENCH_ITER;
    gf128_t *a = malloc(n * sizeof(gf128_t));
    gf128_t *b = malloc(n * sizeof(gf128_t));
    gf128_t *out = malloc(n * sizeof(gf128_t));
    if (!a || !b || !out) {
        fprintf(stderr, "Allocation failed\n");
        return 1;
    }
    // Seed randomness
    srand(0xBEEF);
    for (size_t i = 0; i < n; i++) {
        a[i].hi = ((uint64_t)rand() << 32) | rand();
        a[i].lo = ((uint64_t)rand() << 32) | rand();
        b[i].hi = ((uint64_t)rand() << 32) | rand();
        b[i].lo = ((uint64_t)rand() << 32) | rand();
    }
    printf("Benchmarking GF(2^128) multiply variants (%zu ops)\n", n);
    bench_variant("base", gf128_mul_base, a, b, out, n);
    bench_variant("table", gf128_mul_table, a, b, out, n);
    bench_variant("pclmul", gf128_mul_pclmul, a, b, out, n);
    bench_variant("dispatch", gf128_mul, a, b, out, n);
#ifdef USE_AVX2
    bench_variant("pclmul_avx2", gf128_mul_pclmul_avx2, a, b, out, n);
#endif
#ifdef USE_AVX512
    bench_variant("pclmul_avx512", gf128_mul_pclmul_avx512, a, b, out, n);
#endif
    free(a);
    free(b);
    free(out);
    return 0;
}