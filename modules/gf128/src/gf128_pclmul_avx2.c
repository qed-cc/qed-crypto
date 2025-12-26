// src/gf128_pclmul_avx2.c
#include "gf128.h"
#include <stdint.h>
#include <immintrin.h> // AVX, AVX2, PCLMUL, SSE intrinsics

// --- Start: Duplicated Scalar Reduction Logic ---
// Optimized reduction using PCLMUL (duplicated from gf128_pclmul.c / gf128_pclmul_kara.c)
// Reduces a 256-bit value (lo128, hi128) modulo P(x) = x^128 + x^7 + x^2 + x + 1
// Assumes PCLMUL instruction set is available.
static inline __m128i gf128_reduce_pclmul_scalar_avx2(__m128i lo128, __m128i hi128) {
    const __m128i poly_const = _mm_set_epi64x(0x1, 0xc200000000000000); // Constant derived for GCM reduction
    __m128i tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp1 = _mm_clmulepi64_si128(hi128, poly_const, 0x01);
    tmp2 = _mm_shuffle_epi32(hi128, _MM_SHUFFLE(1, 0, 3, 2));
    tmp3 = _mm_xor_si128(tmp1, tmp2);
    tmp4 = _mm_clmulepi64_si128(tmp3, poly_const, 0x00);
    tmp5 = _mm_shuffle_epi32(tmp3, _MM_SHUFFLE(1, 0, 3, 2));
    tmp6 = _mm_xor_si128(_mm_xor_si128(tmp4, tmp5), lo128);
    return tmp6;
}
// --- End: Duplicated Scalar Reduction Logic ---


// AVX2 implementation for 2 parallel GF(2^128) multiplications
// This version uses standard PCLMUL intrinsics (_mm_clmulepi64_si128)
// as _mm256_clmulepi64_epi128 requires VPCLMULQDQ (AVX512).
void gf128_mul2_pclmul_avx2(const gf128_t a[2], const gf128_t b[2], gf128_t out[2]) {
    // Load operands - treat as separate 128-bit operations
    __m128i x0 = _mm_loadu_si128((const __m128i*)&a[0]);
    __m128i y0 = _mm_loadu_si128((const __m128i*)&b[0]);
    __m128i x1 = _mm_loadu_si128((const __m128i*)&a[1]);
    __m128i y1 = _mm_loadu_si128((const __m128i*)&b[1]);

    // Interleaved 2-way PCLMUL for better pipeline utilization
    __m128i r0_0 = _mm_clmulepi64_si128(x0, y0, 0x00);
    __m128i r0_1 = _mm_clmulepi64_si128(x1, y1, 0x00);
    __m128i r1_0 = _mm_clmulepi64_si128(x0, y0, 0x10);
    __m128i r1_1 = _mm_clmulepi64_si128(x1, y1, 0x10);
    __m128i r2_0 = _mm_clmulepi64_si128(x0, y0, 0x01);
    __m128i r2_1 = _mm_clmulepi64_si128(x1, y1, 0x01);
    __m128i r3_0 = _mm_clmulepi64_si128(x0, y0, 0x11);
    __m128i r3_1 = _mm_clmulepi64_si128(x1, y1, 0x11);

    // Combine cross terms
    __m128i mid0 = _mm_xor_si128(r1_0, r2_0);
    __m128i mid1 = _mm_xor_si128(r1_1, r2_1);

    // Assemble low/high halves
    __m128i lo0 = _mm_xor_si128(r0_0, _mm_slli_si128(mid0, 8));
    __m128i hi0 = _mm_xor_si128(r3_0, _mm_srli_si128(mid0, 8));
    __m128i lo1 = _mm_xor_si128(r0_1, _mm_slli_si128(mid1, 8));
    __m128i hi1 = _mm_xor_si128(r3_1, _mm_srli_si128(mid1, 8));

    // Reduction
    __m128i res0 = gf128_reduce_pclmul_scalar_avx2(lo0, hi0);
    __m128i res1 = gf128_reduce_pclmul_scalar_avx2(lo1, hi1);

    // Store results
    _mm_storeu_si128((__m128i*)&out[0], res0);
    _mm_storeu_si128((__m128i*)&out[1], res1);
}

// Scalar AVX2 wrapper (calls the 2-way version)
gf128_t gf128_mul_pclmul_avx2(gf128_t a, gf128_t b) {
    // Use attribute for alignment in C99
    gf128_t a2[2] __attribute__((aligned(32)));
    gf128_t b2[2] __attribute__((aligned(32)));
    gf128_t out2[2] __attribute__((aligned(32)));

    // Duplicate inputs
    a2[0] = a;
    a2[1] = a; // Using duplicate input for scalar call
    b2[0] = b;
    b2[1] = b;

    gf128_mul2_pclmul_avx2(a2, b2, out2);

    return out2[0]; // Return the result for the first lane
}

// Provide empty stubs if AVX2 or PCLMUL are not enabled,
// to avoid linker errors if headers declare them.
// Note: These conditions might need adjustment based on CMake logic.
// We check USE_AVX2 (set by CMake when AVX2 is enabled) and
// HAVE_PCLMUL (set by CMake when PCLMUL is enabled).
#if !defined(USE_AVX2)
#warning "Compiling AVX2 stubs" // Add warning for debugging build issues
// Only define stubs if the header actually declared them (via USE_AVX2)
#ifdef USE_AVX2
void gf128_mul2_pclmul_avx2(const gf128_t a[2], const gf128_t b[2], gf128_t out[2]) {
    // Fallback or error
    out[0] = gf128_mul(a[0], b[0]); // Use generic dispatch as fallback?
    out[1] = gf128_mul(a[1], b[1]);
}
gf128_t gf128_mul_pclmul_avx2(gf128_t a, gf128_t b) {
     return gf128_mul(a, b); // Use generic dispatch
}
#endif // USE_AVX2
#endif // Stubs
