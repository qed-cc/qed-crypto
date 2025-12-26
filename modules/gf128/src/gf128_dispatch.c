/*
 * Dispatch-based generic multiply for GF(2^128).
 * Selects the fastest available backend (PCLMUL or table) at load time.
 */
#include "gf128.h"
#include <stdbool.h> // for bool
#include "cpu_features.h"

typedef gf128_t (*gf128_mul_fn)(gf128_t, gf128_t);

/* Default to table-driven implementation */
static gf128_mul_fn mul_fn = gf128_mul_table;

/* Constructor attribute to initialize mul_fn before use */
static void __attribute__((constructor)) gf128_init_mul(void) {
    /* Dispatch to best available GF(2^128) multiply */
#if defined(USE_AVX512)
    if (gf128_has_avx512()) {
        mul_fn = gf128_mul_pclmul_avx512;
        return;
    }
#endif
#if defined(USE_AVX2)
    if (gf128_has_avx2()) {
        mul_fn = gf128_mul_pclmul_avx2;
        return;
    }
#endif
    if (gf128_has_pclmul()) mul_fn = gf128_mul_pclmul;
    else mul_fn = gf128_mul_base;
}

/* Public multiply entry point */
gf128_t gf128_mul(gf128_t a, gf128_t b) {
    return mul_fn(a, b);
}

