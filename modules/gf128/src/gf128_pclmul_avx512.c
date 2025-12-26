/*
 * AVX-512 accelerated GF(2^128) multiplication using VPCLMULQDQ.
 * Computes four independent multiplications in parallel using ZMM registers.
 * Based on Karatsuba method: 3 VPCLMULQDQs per 4x128-bit multiply.
 */
#include "gf128.h"

#ifdef ENABLE_PCLMUL // Require PCLMUL intrinsics
#ifdef USE_AVX512     // Only compile if AVX512 is requested via CMake

// Function attributes for AVX-512 carry-less multiply kernels
#ifdef __GNUC__
# define AVX512_FUNC_ATTR __attribute__((always_inline, target("avx512f,pclmul")))
#else
# define AVX512_FUNC_ATTR
#endif
#include <immintrin.h> // AVX-512 intrinsics

// Load four gf128_t into a ZMM register (unaligned)
static AVX512_FUNC_ATTR __m512i load4_gf128(const gf128_t * __restrict a) {
    return _mm512_loadu_si512((const __m512i*)a);
}

// Store a ZMM register into four gf128_t (unaligned)
static AVX512_FUNC_ATTR void store4_gf128(gf128_t * __restrict out, __m512i zmm) {
    _mm512_storeu_si512((__m512i*)out, zmm);
}

// Barrett reduction modulo x^128 + x^7 + x^2 + x + 1 (vectorized for 4 lanes)
// Select best reduction: VNNI > GFNI > PCLMUL fallback
#ifdef USE_VNNI
static AVX512_FUNC_ATTR __m512i gf128_reduce_avx512(__m512i P0, __m512i P1) {
    // VNNI-accelerated reduction: affine multiply in GF(2^8)
    const __m512i Rb = _mm512_set1_epi8(0xe1);
    __m512i t = _mm512_gf2p8affine_epi64_epi8(P1, Rb, 0);
    return _mm512_xor_si512(P0, t);
}
#elif defined(USE_GFNI)
// GFNI-accelerated reduction: result = P0 ^ (P1 * r(x)) where r(x)=x^7+x^2+x+1
static AVX512_FUNC_ATTR __m512i gf128_reduce_avx512(__m512i P0, __m512i P1) {
    const __m512i Rb = _mm512_set1_epi8(0xe1);
    __m512i t = _mm512_gf2p8mul_epi8(P1, Rb);
    return _mm512_xor_si512(P0, t);
}
#else
// PCLMUL-based reduction fallback
static AVX512_FUNC_ATTR __m512i gf128_reduce_avx512(__m512i P0, __m512i P1) {
    const __m128i poly128 = _mm_set_epi64x(0x1, 0xc200000000000000);
    const __m512i poly512 = _mm512_broadcast_i32x4(poly128);
    __m512i t1 = _mm512_clmulepi64_epi128(P1, poly512, 0x01);
    __m512i t2 = _mm512_alignr_epi8(P1, P1, 8);
    __m512i t3 = _mm512_xor_si512(t1, t2);
    __m512i t4 = _mm512_clmulepi64_epi128(t3, poly512, 0x00);
    __m512i t5 = _mm512_alignr_epi8(t3, t3, 8);
    return _mm512_xor_si512(_mm512_xor_si512(t4, t5), P0);
}
#endif

/**
 * Batched 4-way AVX-512 VPCLMULQDQ multiply: out[i] = a[i] * b[i] for i=0..3
 */
__attribute__((target("avx512f,pclmul")))
void gf128_mul4_pclmul_avx512(const gf128_t * __restrict a,
                              const gf128_t * __restrict b,
                              gf128_t * __restrict out) {
    // Load operands into ZMM registers
    __m512i x = load4_gf128(a);
    __m512i y = load4_gf128(b);

    // Karatsuba steps (vectorized for 4 lanes)
    // d0 = a_lo * b_lo (lanes 0..3)
    __m512i d0 = _mm512_clmulepi64_epi128(x, y, 0x00);
    // d2 = a_hi * b_hi (lanes 0..3)
    __m512i d2 = _mm512_clmulepi64_epi128(x, y, 0x11);

    // Compute e = a_lo ^ a_hi, f = b_lo ^ b_hi for all 4 lanes simultaneously
    // Use vpxorq for AVX-512
    __m512i x_hi_dup = _mm512_shuffle_epi32(x, _MM_SHUFFLE(3, 2, 3, 2)); // Duplicate hi 64 bits of each 128
    __m512i e = _mm512_xor_si512(x, x_hi_dup); // Contains { *, e3, *, e2, *, e1, *, e0 }

    __m512i y_hi_dup = _mm512_shuffle_epi32(y, _MM_SHUFFLE(3, 2, 3, 2)); // Duplicate hi 64 bits of each 128
    __m512i f = _mm512_xor_si512(y, y_hi_dup); // Contains { *, f3, *, f2, *, f1, *, f0 }

    // d1 = e * f (lanes 0..3) - using only low 64 bits (imm=0x00)
    __m512i d1 = _mm512_clmulepi64_epi128(e, f, 0x00);

    // Combine mid = d1 ^ d0 ^ d2
    __m512i mid = _mm512_xor_si512(_mm512_xor_si512(d1, d0), d2);

    // Assemble 256-bit product P = { P1, P0 } for each lane
    // P0 = d0 ^ (mid << 64)
    __m512i mid_shift_left = _mm512_bslli_epi128(mid, 8); // Shift left by 64 bits (8 bytes)
    __m512i P0 = _mm512_xor_si512(d0, mid_shift_left);
    // P1 = d2 ^ (mid >> 64)
    __m512i mid_shift_right = _mm512_bsrli_epi128(mid, 8); // Shift right by 64 bits (8 bytes)
    __m512i P1 = _mm512_xor_si512(d2, mid_shift_right);

    // Reduce the 256-bit products (P1:P0) to 128 bits for each lane
    __m512i result = gf128_reduce_avx512(P0, P1);

    // Store result
    store4_gf128(out, result);
}

/**
 * Scalar AVX-512 wrapper: uses four-way AVX-512 Karatsuba PCLMUL.
 * Broadcasts inputs across lanes.
 */
__attribute__((target("avx512f,pclmul")))
gf128_t gf128_mul_pclmul_avx512(gf128_t a, gf128_t b) {
    // Use aligned buffers if possible
    gf128_t a4[4] __attribute__((aligned(64)));
    gf128_t b4[4] __attribute__((aligned(64)));
    gf128_t out4[4] __attribute__((aligned(64)));

    // Broadcast scalar inputs to all 4 lanes
    for (int i = 0; i < 4; ++i) {
        a4[i] = a;
        b4[i] = b;
    }

    gf128_mul4_pclmul_avx512(a4, b4, out4);
    return out4[0]; // Return the result from the first lane
}

/**
 * Super-batched 8-way AVX-512 PCLMUL multiply: interleaves two 4-way batches to hide latency.
 * Processes elements 0..3 and 4..7 in a single pipeline.
 */
__attribute__((target("avx512f,pclmul")))
void gf128_mul8_pclmul_avx512_super(const gf128_t * __restrict a,
                                    const gf128_t * __restrict b,
                                    gf128_t * __restrict out) {
    // Load two batches of 4
    __m512i x0 = load4_gf128(a);
    __m512i y0 = load4_gf128(b);
    __m512i x1 = load4_gf128(a + 4);
    __m512i y1 = load4_gf128(b + 4);
    // Karatsuba CLMUL for batch0 and batch1 interleaved
    __m512i d0_0 = _mm512_clmulepi64_epi128(x0, y0, 0x00);
    __m512i d0_1 = _mm512_clmulepi64_epi128(x1, y1, 0x00);
    __m512i d2_0 = _mm512_clmulepi64_epi128(x0, y0, 0x11);
    __m512i d2_1 = _mm512_clmulepi64_epi128(x1, y1, 0x11);
    __m512i e0 = _mm512_xor_si512(x0, _mm512_shuffle_epi32(x0, _MM_SHUFFLE(3,2,3,2)));
    __m512i e1 = _mm512_xor_si512(x1, _mm512_shuffle_epi32(x1, _MM_SHUFFLE(3,2,3,2)));
    __m512i f0 = _mm512_xor_si512(y0, _mm512_shuffle_epi32(y0, _MM_SHUFFLE(3,2,3,2)));
    __m512i f1 = _mm512_xor_si512(y1, _mm512_shuffle_epi32(y1, _MM_SHUFFLE(3,2,3,2)));
    __m512i d1_0 = _mm512_clmulepi64_epi128(e0, f0, 0x00);
    __m512i d1_1 = _mm512_clmulepi64_epi128(e1, f1, 0x00);
    __m512i mid0 = _mm512_xor_si512(_mm512_xor_si512(d1_0, d0_0), d2_0);
    __m512i mid1 = _mm512_xor_si512(_mm512_xor_si512(d1_1, d0_1), d2_1);
    __m512i P0_0 = _mm512_xor_si512(d0_0, _mm512_bslli_epi128(mid0, 8));
    __m512i P0_1 = _mm512_xor_si512(d0_1, _mm512_bslli_epi128(mid1, 8));
    __m512i P1_0 = _mm512_xor_si512(d2_0, _mm512_bsrli_epi128(mid0, 8));
    __m512i P1_1 = _mm512_xor_si512(d2_1, _mm512_bsrli_epi128(mid1, 8));
    // Reduce
    __m512i r0 = gf128_reduce_avx512(P0_0, P1_0);
    __m512i r1 = gf128_reduce_avx512(P0_1, P1_1);
    // Store two batches of 4
    store4_gf128(out, r0);
    store4_gf128(out + 4, r1);
}

#endif // USE_AVX512
#endif // ENABLE_PCLMUL

// Stubs for non-AVX512 builds
#if !defined(ENABLE_PCLMUL) || !defined(USE_AVX512)
#include "gf128.h"

#ifdef USE_AVX512 // Match header condition
void gf128_mul4_pclmul_avx512(const gf128_t a[4], const gf128_t b[4], gf128_t out[4]) {
    for(int i=0; i<4; ++i) out[i] = gf128_zero();
}
gf128_t gf128_mul_pclmul_avx512(gf128_t a, gf128_t b) {
    (void)a; (void)b;
    return gf128_zero();
}
#endif // USE_AVX512

#endif // !ENABLE_PCLMUL || !USE_AVX512

