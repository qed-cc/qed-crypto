/*
 * Experimental pure GFNI-based GF(2^128) multiplication kernel.
 * Currently implemented as a wrapper around the optimized PCLMUL kernel.
 * Future work: replace PCLMUL calls with GFNI-only polynomial multiply.
 */
#include "gf128.h"

// Experimental GFNI-accelerated scalar multiply: PCLMUL + GFNI reduction
#ifdef USE_GFNI_MUL
#include "gf128.h"
#include <immintrin.h>
#ifdef __GNUC__
# define GFNI_FUNC_ATTR __attribute__((always_inline))
#else
# define GFNI_FUNC_ATTR
#endif

/**
 * gf128_mul_gfni: optimized GF(2^128) multiply using PCLMUL for partial products
 * and a single GFNI reduction (_mm_gf2p8mul_epi8) per block.
 */
GFNI_FUNC_ATTR
gf128_t gf128_mul_gfni(gf128_t a, gf128_t b) {
    // Load 128-bit operands: [hi|lo]
    __m128i x = _mm_set_epi64x((long long)a.hi, (long long)a.lo);
    __m128i y = _mm_set_epi64x((long long)b.hi, (long long)b.lo);
    // Carry-less multiply: 4 partial products
    __m128i r0 = _mm_clmulepi64_si128(x, y, 0x00);
    __m128i r1 = _mm_clmulepi64_si128(x, y, 0x10);
    __m128i r2 = _mm_clmulepi64_si128(x, y, 0x01);
    __m128i r3 = _mm_clmulepi64_si128(x, y, 0x11);
    // Karatsuba combine
    __m128i mid   = _mm_xor_si128(r1, r2);
    __m128i lo128 = _mm_xor_si128(r0, _mm_slli_si128(mid, 8));
    __m128i hi128 = _mm_xor_si128(r3, _mm_srli_si128(mid, 8));
    // GFNI reduction: Rb = 0xe1 (x^7+x^2+x+1)
    const __m128i Rb = _mm_set1_epi8((char)0xe1);
    __m128i red = _mm_gf2p8mul_epi8(hi128, Rb);
    __m128i out = _mm_xor_si128(lo128, red);
    // Store and reorder to gf128_t
    struct { uint64_t lo, hi; } tmp;
    _mm_storeu_si128((__m128i*)&tmp, out);
    gf128_t result;
    result.hi = tmp.lo;
    result.lo = tmp.hi;
    return result;
}
#else
gf128_t gf128_mul_gfni(gf128_t a, gf128_t b) {
    // Fallback to generic multiply
    return gf128_mul(a, b);
}
#endif