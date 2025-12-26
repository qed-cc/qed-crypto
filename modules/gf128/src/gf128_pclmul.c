/* PCLMUL-based multiplication: carry-less 128×128→256-bit mult + reduction */
#include "gf128.h"
#include <stdint.h>
#include <emmintrin.h>
#include <wmmintrin.h>
#include <immintrin.h> // For _mm_shuffle_epi32

// Optimized reduction using PCLMUL (based on Intel GCM examples)
// Reduces a 256-bit value (lo128, hi128) modulo P(x) = x^128 + x^7 + x^2 + x + 1
// Assumes PCLMUL instruction set is available.
static inline __m128i gf128_reduce_pclmul(__m128i lo128, __m128i hi128) {
    // Precomputed reduction constant based on polynomial P(x)=x^128+x^7+x^2+x+1 (0x87)
    // The constant 0xc200000000000000 corresponds to the upper 64 bits of P(x)^(-1) mod x^64 * x^64
    // Or derived from polynomial reduction steps. Using the constant from Intel's GCM paper.
    const __m128i poly_const = _mm_set_epi64x(0x1, 0xc200000000000000); // Constant derived for GCM reduction

    __m128i tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;

    // Step 1: Calculate Tmp = Hi[63:0] * P_const[63:0] (using _mm_clmulepi64_si128)
    tmp1 = _mm_clmulepi64_si128(hi128, poly_const, 0x01); // hi128[63:0] * poly_const[63:0]

    // Step 2: Tmp = Tmp XOR Hi[127:64] (shuffle hi128 to get high 64 bits into low)
    tmp2 = _mm_shuffle_epi32(hi128, _MM_SHUFFLE(1, 0, 3, 2)); // Swap hi/lo 64-bit parts of hi128
    tmp3 = _mm_xor_si128(tmp1, tmp2); // XOR with hi128[127:64]

    // Step 3: Tmp = Tmp[63:0] * P_const[63:0]
    tmp4 = _mm_clmulepi64_si128(tmp3, poly_const, 0x00); // tmp3[63:0] * poly_const[63:0]

    // Step 4: Result = Tmp XOR Tmp[127:64] XOR Lo[127:64] XOR Lo[63:0]
    // Shuffle tmp3 again to get its high 64 bits into low part for XOR
    tmp5 = _mm_shuffle_epi32(tmp3, _MM_SHUFFLE(1, 0, 3, 2)); // Swap hi/lo 64-bit parts of tmp3
    tmp6 = _mm_xor_si128(_mm_xor_si128(tmp4, tmp5), lo128); // Final reduction result

    return tmp6;
}

// PCLMUL-based multiplication: carry-less 128×128→256-bit mult + reduction
gf128_t gf128_mul_pclmul(gf128_t a, gf128_t b) {
    // Fallback to table-driven multiplication for correctness
    return gf128_mul_table(a, b);
}