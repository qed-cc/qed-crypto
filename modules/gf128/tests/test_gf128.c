#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <time.h>
#include "gf128.h"

int main(void) {
    int failures = 0;
    /* Seed for reproducible randomized tests */
    srand(0xC0FFEE);

    gf128_t one = {0, 1};
    gf128_t two = {0, 2};

    /* Test addition: 1 + 2 = 3 */
    gf128_t sum = gf128_add(one, two);
    if (sum.hi != 0 || sum.lo != 3) {
        printf("Addition test failed: expected hi=0 lo=3, got hi=%" PRIx64 " lo=%" PRIx64 "\n", sum.hi, sum.lo);
        failures++;
    }

    /* Test multiplication by one: 1 * 1 = 1 */
    gf128_t r = gf128_mul_base(one, one);
    if (r.hi != one.hi || r.lo != one.lo) {
        printf("Multiplication by one failed: expected hi=%" PRIx64 " lo=%" PRIx64 ", got hi=%" PRIx64 " lo=%" PRIx64 "\n", one.hi, one.lo, r.hi, r.lo);
        failures++;
    }

    /* Test simple multiply: 2 * 2 = 4 */
    r = gf128_mul_base(two, two);
    if (r.hi != 0 || r.lo != 4) {
        printf("Multiplication 2*2 failed: expected hi=0 lo=4, got hi=%" PRIx64 " lo=%" PRIx64 "\n", r.hi, r.lo);
        failures++;
    }

    /* Test table-driven multiplication matches base implementation */
    /* 1 * 1 = 1 */
    r = gf128_mul_table(one, one);
    if (r.hi != one.hi || r.lo != one.lo) {
        printf("Table mul 1*1 failed: expected hi=%" PRIx64 " lo=%" PRIx64 ", got hi=%" PRIx64 " lo=%" PRIx64 "\n",
               one.hi, one.lo, r.hi, r.lo);
        failures++;
    }
    /* 2 * 2 = 4 */
    r = gf128_mul_table(two, two);
    if (r.hi != 0 || r.lo != 4) {
        printf("Table mul 2*2 failed: expected hi=0 lo=4, got hi=%" PRIx64 " lo=%" PRIx64 "\n", r.hi, r.lo);
        failures++;
    }
    /* Randomized consistency test */
    gf128_t x = {0x0123456789abcdefULL, 0xfedcba9876543210ULL};
    gf128_t y = {0xf0e1d2c3b4a59687ULL, 0x76543210fedcba98ULL};
    gf128_t base = gf128_mul_base(x, y);
    gf128_t table = gf128_mul_table(x, y);
    if (base.hi != table.hi || base.lo != table.lo) {
        printf("Table mul mismatch: base hi=0x%016" PRIx64 " lo=0x%016" PRIx64
               ", table hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               base.hi, base.lo, table.hi, table.lo);
        failures++;
    }
    /* Commutativity check */
    gf128_t table2 = gf128_mul_table(y, x);
    if (base.hi != table2.hi || base.lo != table2.lo) {
        printf("Table mul not commutative: y*x hi=0x%016" PRIx64 " lo=0x%016" PRIx64
               " expected hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               table2.hi, table2.lo, base.hi, base.lo);
        failures++;
    }

    /* Test PCLMUL-based multiplication matches base implementation */
    /* 1 * 1 = 1 */
    r = gf128_mul_pclmul(one, one);
    if (r.hi != one.hi || r.lo != one.lo) {
        printf("PCLMUL mul 1*1 failed: expected hi=%" PRIx64 " lo=%" PRIx64 ", got hi=%" PRIx64 " lo=%" PRIx64 "\n",
               one.hi, one.lo, r.hi, r.lo);
        failures++;
    }
    /* 2 * 2 = 4 */
    r = gf128_mul_pclmul(two, two);
    if (r.hi != 0 || r.lo != 4) {
        printf("PCLMUL mul 2*2 failed: expected hi=0 lo=4, got hi=%" PRIx64 " lo=%" PRIx64 "\n",
               r.hi, r.lo);
        failures++;
    }
    /* Consistency with base */
    gf128_t pcl = gf128_mul_pclmul(x, y);
    if (pcl.hi != base.hi || pcl.lo != base.lo) {
        printf("PCLMUL mul mismatch: base hi=0x%016" PRIx64 " lo=0x%016" PRIx64
               ", pcl hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               base.hi, base.lo, pcl.hi, pcl.lo);
        failures++;
    }
    /* Commutativity y*x */
    gf128_t pcl2 = gf128_mul_pclmul(y, x);
    if (pcl2.hi != base.hi || pcl2.lo != base.lo) {
        printf("PCLMUL mul not commutative: y*x hi=0x%016" PRIx64 " lo=0x%016" PRIx64
               " expected hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               pcl2.hi, pcl2.lo, base.hi, base.lo);
        failures++;
    }

    #if 0
    /* Context-based table-driven multiplication tests */
    /* Test gf128_mul_table256 via context and gf128_mul_ctx_mul */
    {
        gf128_mul_ctx_t ctx;
        gf128_mul_ctx_init(&ctx, x);
        gf128_t ctx_res = gf128_mul_ctx_mul(&ctx, y);
        if (ctx_res.hi != base.hi || ctx_res.lo != base.lo) {
            printf("Context-based mul mismatch: expected hi=0x%016" PRIx64 " lo=0x%016" PRIx64
                   ", got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
                   base.hi, base.lo, ctx_res.hi, ctx_res.lo);
            failures++;
        }
        /* Test dispatch and optimized variants against base result */
        {
            /* Generic dispatch */
            gf128_t m_disp = gf128_mul(ra, rb);
            if (!gf128_eq(m0, m_disp)) {
                printf("Random dispatch mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
        {
            /* Table256 context multiply */
            gf128_mul_ctx_t ctx;
            gf128_mul_ctx_init(&ctx, ra);
            gf128_t m_ctx = gf128_mul_ctx_mul(&ctx, rb);
            if (!gf128_eq(m0, m_ctx)) {
                printf("Random ctx mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
#ifdef USE_PCLMUL_KARATSUBA
        {
            /* Karatsuba PCLMUL variant */
            gf128_t m_kara = gf128_mul_pclmul_kara(ra, rb);
            if (!gf128_eq(m0, m_kara)) {
                printf("Random karatsuba mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
#endif
#ifdef USE_AVX2
        {
            /* Scalar AVX2 variant */
            gf128_t m_avx2 = gf128_mul_pclmul_avx2(ra, rb);
            if (!gf128_eq(m0, m_avx2)) {
                printf("Random AVX2 mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
#endif
#ifdef USE_AVX512
        {
            /* Scalar AVX-512 variant */
            gf128_t m_avx512 = gf128_mul_pclmul_avx512(ra, rb);
            if (!gf128_eq(m0, m_avx512)) {
                printf("Random AVX512 mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
#endif
#ifdef USE_GFNI_MUL
        {
            /* GFNI-only variant */
            gf128_t m_gfni = gf128_mul_gfni(ra, rb);
            if (!gf128_eq(m0, m_gfni)) {
                printf("Random GFNI mul mismatch at iteration %d\n", i);
                failures++;
                break;
            }
        }
    #endif
    }
    #endif
    /* Inversion tests */
    /* inv(1) = 1 */
    gf128_t inv1 = gf128_inv(one);
    if (inv1.hi != one.hi || inv1.lo != one.lo) {
        printf("Inversion failed on 1: got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               inv1.hi, inv1.lo);
        failures++;
    }
    /* inv(2) * 2 = 1 */
    gf128_t inv2 = gf128_inv(two);
    r = gf128_mul_base(inv2, two);
    if (r.hi != one.hi || r.lo != one.lo) {
        printf("Inversion failed on 2: got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               r.hi, r.lo);
        failures++;
    }
    /* inv(x) * x = 1 */
    gf128_t invx = gf128_inv(x);
    r = gf128_mul_base(invx, x);
    if (r.hi != one.hi || r.lo != one.lo) {
        printf("Inversion failed on x: got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               r.hi, r.lo);
        failures++;
    }

    /* Division tests: a/1 = a, a/a = 1 */
    gf128_t d1 = gf128_div(x, one);
    if (d1.hi != x.hi || d1.lo != x.lo) {
        printf("Division failed: x/1 got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               d1.hi, d1.lo);
        failures++;
    }
    gf128_t d2 = gf128_div(x, x);
    if (d2.hi != one.hi || d2.lo != one.lo) {
        printf("Division failed: x/x got hi=0x%016" PRIx64 " lo=0x%016" PRIx64 "\n",
               d2.hi, d2.lo);
        failures++;
    }
    /* Additional edge-case tests */
    gf128_t zero = {0, 0};
    gf128_t all1 = { (uint64_t)-1, (uint64_t)-1 };
    /* Addition with zero: zero + x = x */
    if (gf128_add(zero, x).hi != x.hi || gf128_add(zero, x).lo != x.lo) failures++;
    if (gf128_add(all1, zero).hi != all1.hi || gf128_add(all1, zero).lo != all1.lo) failures++;
    /* Zero multiplication: zero * x = zero */
    if (gf128_mul_base(zero, x).hi || gf128_mul_base(zero, x).lo) failures++;
    if (gf128_mul_table(zero, x).hi || gf128_mul_table(zero, x).lo) failures++;
    if (gf128_mul_pclmul(zero, x).hi || gf128_mul_pclmul(zero, x).lo) failures++;
    /* All-ones multiplication consistency */
    gf128_t base_all = gf128_mul_base(all1, all1);
    gf128_t tbl_all = gf128_mul_table(all1, all1);
    gf128_t pcl_all = gf128_mul_pclmul(all1, all1);
    if (base_all.hi != tbl_all.hi || base_all.lo != tbl_all.lo) failures++;
    if (base_all.hi != pcl_all.hi || base_all.lo != pcl_all.lo) failures++;
    /* Division by zero yields zero */
    if (gf128_div(x, zero).hi || gf128_div(x, zero).lo) failures++;
    /* Zero divided by x yields zero */
    if (gf128_div(zero, x).hi || gf128_div(zero, x).lo) failures++;
    /* Inversion of zero yields zero */
    if (!gf128_is_zero(gf128_inv(zero))) {
        printf("Inversion of zero failed: expected zero\n");
        failures++;
    }
    /* Comparison and zero-check tests */
    if (!gf128_is_zero(zero)) {
        printf("gf128_is_zero failed on zero\n"); failures++;
    }
    if (gf128_is_zero(one)) {
        printf("gf128_is_zero failed on one\n"); failures++;
    }
    if (!gf128_eq(x, x)) {
        printf("gf128_eq failed on equal elements\n"); failures++;
    }
    if (gf128_eq(x, y)) {
        printf("gf128_eq failed on unequal elements\n"); failures++;
    }
    /* Little-endian serialization round-trip */
    {
        uint8_t buf[16];
        gf128_to_le(x, buf);
        gf128_t xr = gf128_from_le(buf);
        if (!gf128_eq(xr, x)) {
            printf("LE serialization round-trip failed\n"); failures++;
        }
    }
#ifdef USE_AVX2
    /* Test AVX2 2-way multiply correctness */
    for (int i = 0; i < 10; i++) {
        gf128_t a2[2], b2[2], out2[2];
        for (int j = 0; j < 2; j++) {
            a2[j].hi = ((uint64_t)rand() << 32) | rand();
            a2[j].lo = ((uint64_t)rand() << 32) | rand();
            b2[j].hi = ((uint64_t)rand() << 32) | rand();
            b2[j].lo = ((uint64_t)rand() << 32) | rand();
        }
        gf128_mul2_pclmul_avx2(a2, b2, out2);
        for (int j = 0; j < 2; j++) {
            gf128_t expect = gf128_mul_base(a2[j], b2[j]);
            if (!gf128_eq(expect, out2[j])) {
                printf("AVX2 mul2 mismatch at lane %d\n", j);
                failures++;
            }
        }
    }
#endif
#ifdef USE_AVX512
    /* Test AVX-512 4-way multiply correctness */
    for (int i = 0; i < 5; i++) {
        gf128_t a4[4], b4[4], out4[4];
        for (int j = 0; j < 4; j++) {
            a4[j].hi = ((uint64_t)rand() << 32) | rand();
            a4[j].lo = ((uint64_t)rand() << 32) | rand();
            b4[j].hi = ((uint64_t)rand() << 32) | rand();
            b4[j].lo = ((uint64_t)rand() << 32) | rand();
        }
        gf128_mul4_pclmul_avx512(a4, b4, out4);
        for (int j = 0; j < 4; j++) {
            gf128_t expect = gf128_mul_base(a4[j], b4[j]);
            if (!gf128_eq(expect, out4[j])) {
                printf("AVX512 mul4 mismatch at lane %d\n", j);
                failures++;
            }
        }
    }
    #endif
    /* AVX2 2-way multiply correctness tests */
    #ifdef USE_AVX2
    for (int k = 0; k < 10; k++) {
        gf128_t a2[2], b2[2], o2[2];
        for (int j = 0; j < 2; j++) {
            a2[j].hi = ((uint64_t)rand() << 32) | rand();
            a2[j].lo = ((uint64_t)rand() << 32) | rand();
            b2[j].hi = ((uint64_t)rand() << 32) | rand();
            b2[j].lo = ((uint64_t)rand() << 32) | rand();
        }
        gf128_mul2_pclmul_avx2(a2, b2, o2);
        for (int j = 0; j < 2; j++) {
            gf128_t e = gf128_mul_base(a2[j], b2[j]);
            if (!gf128_eq(e, o2[j])) { failures++; printf("AVX2 lane %d test failed\n", j); }
        }
    }
    #endif
    /* AVX-512 4-way multiply correctness tests */
    #ifdef USE_AVX512
    for (int k = 0; k < 5; k++) {
        gf128_t a4[4], b4[4], o4[4];
        for (int j = 0; j < 4; j++) {
            a4[j].hi = ((uint64_t)rand() << 32) | rand();
            a4[j].lo = ((uint64_t)rand() << 32) | rand();
            b4[j].hi = ((uint64_t)rand() << 32) | rand();
            b4[j].lo = ((uint64_t)rand() << 32) | rand();
        }
        gf128_mul4_pclmul_avx512(a4, b4, o4);
        for (int j = 0; j < 4; j++) {
            gf128_t e = gf128_mul_base(a4[j], b4[j]);
            if (!gf128_eq(e, o4[j])) { failures++; printf("AVX512 lane %d test failed\n", j); }
        }
    }
    #endif
    /* Test AVX-512 8-way super-batch multiply correctness */
    #ifdef USE_AVX512
    for (int i = 0; i < 5; i++) {
        gf128_t a8[8], b8[8], out8[8];
        for (int j = 0; j < 8; j++) {
            a8[j].hi = ((uint64_t)rand() << 31) | rand();
            a8[j].lo = ((uint64_t)rand() << 31) | rand();
            b8[j].hi = ((uint64_t)rand() << 31) | rand();
            b8[j].lo = ((uint64_t)rand() << 31) | rand();
        }
        gf128_mul8_pclmul_avx512_super(a8, b8, out8);
        for (int j = 0; j < 8; j++) {
            gf128_t expect = gf128_mul_base(a8[j], b8[j]);
            if (!gf128_eq(expect, out8[j])) {
                printf("AVX512 super8 mismatch at lane %d iteration %d\n", j, i);
                failures++;
            }
        }
    }
    #endif
    /* Big-endian serialization round-trip */
    {
        uint8_t buf_be[16];
        gf128_to_be(x, buf_be);
        gf128_t xbe = gf128_from_be(buf_be);
        if (!gf128_eq(xbe, x)) {
            printf("BE serialization round-trip failed\n"); failures++;
        }
    }
    /* Generic multiply (gf128_mul) simple tests */
    {
        /* 1 * 1 = 1 */
        gf128_t gen = gf128_mul(one, one);
        if (!gf128_eq(gen, one)) {
            printf("Generic gf128_mul 1*1 failed\n"); failures++;
        }
        /* 2 * 2 = 4 */
        gf128_t two4 = {0, 4};
        gen = gf128_mul(two, two);
        if (!gf128_eq(gen, two4)) {
            printf("Generic gf128_mul 2*2 failed\n"); failures++;
        }
    }
    /* Generic multiply consistency with base implementation */
    {
        gf128_t mgen = gf128_mul(x, y);
        gf128_t mbase = gf128_mul_base(x, y);
        if (!gf128_eq(mgen, mbase)) {
            printf("Generic gf128_mul mismatch for x,y\n"); failures++;
        }
    }

    /* Randomized property-based tests */
    for (int i = 0; i < 1000; i++) {
        /* Generate random field elements */
        gf128_t ra, rb;
        ra.hi = ((uint64_t)rand() << 31) | rand();
        ra.lo = ((uint64_t)rand() << 31) | rand();
        rb.hi = ((uint64_t)rand() << 31) | rand();
        rb.lo = ((uint64_t)rand() << 31) | rand();
        /* Test multiplication consistency */
        gf128_t m0 = gf128_mul_base(ra, rb);
        gf128_t m1 = gf128_mul_table(ra, rb);
        gf128_t m2 = gf128_mul_pclmul(ra, rb);
        if (m0.hi != m1.hi || m0.lo != m1.lo) {
            printf("Random mul mismatch base/table at iteration %d\n", i);
            failures++;
            break;
        }
        if (m0.hi != m2.hi || m0.lo != m2.lo) {
            printf("Random mul mismatch base/pclmul at iteration %d\n", i);
            failures++;
            break;
        }
        /* Test inversion/division for non-zero rb */
        if (!(rb.hi == 0 && rb.lo == 0)) {
            gf128_t invb = gf128_inv(rb);
            gf128_t mi = gf128_mul_base(invb, rb);
            if (mi.hi != one.hi || mi.lo != one.lo) {
                printf("Random inversion failed at iteration %d\n", i);
                failures++;
                break;
            }
            gf128_t div = gf128_div(ra, rb);
            gf128_t m3 = gf128_mul_base(div, rb);
            if (m3.hi != ra.hi || m3.lo != ra.lo) {
                printf("Random division failed at iteration %d\n", i);
                failures++;
                break;
            }
        }
    }
    if (failures) {
        printf("%d tests failed\n", failures);
        return 1;
    }
    printf("All tests passed\n");
    return 0;
}