#include <stdio.h>
#include <inttypes.h>
#include "gf128.h"

int main(void) {
    gf128_t a = {0x1ULL, 0x2ULL};
    gf128_t b = {0x0ULL, 0x3ULL};
    // Reference bitwise multiply
    gf128_t r_base = gf128_mul_base(a, b);
    printf("base mul       : %016" PRIx64 "%016" PRIx64 "\n", r_base.hi, r_base.lo);
    // Table-driven multiply
    gf128_t r_table = gf128_mul_table(a, b);
    printf("table mul      : %016" PRIx64 "%016" PRIx64 "\n", r_table.hi, r_table.lo);
    // Context-based multiply
    gf128_mul_ctx_t ctx;
    gf128_mul_ctx_init(&ctx, a);
    gf128_t r_ctx = gf128_mul_ctx_mul(&ctx, b);
    printf("ctx-based mul  : %016" PRIx64 "%016" PRIx64 "\n", r_ctx.hi, r_ctx.lo);
    // Generic multiply (dynamic dispatch)
    gf128_t r_gen = gf128_mul(a, b);
    printf("generic mul    : %016" PRIx64 "%016" PRIx64 "\n", r_gen.hi, r_gen.lo);
    // PCLMUL-based multiply
    if (gf128_has_pclmul()) {
        gf128_t r_pcl = gf128_mul_pclmul(a, b);
        printf("pclmul mul     : %016" PRIx64 "%016" PRIx64 "\n", r_pcl.hi, r_pcl.lo);
    } else {
        printf("pclmul not supported, generic mul used\n");
    }
    return 0;
}