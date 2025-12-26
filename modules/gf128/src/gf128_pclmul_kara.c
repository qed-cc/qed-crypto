 // src/gf128_pclmul_kara.c
 #include "gf128.h"
 #include <stdint.h>
 #include <wmmintrin.h> // For PCLMULQDQ intrinsics
 #include <emmintrin.h> // For SSE2 intrinsics (_mm_xor_si128, etc.)
 #include <smmintrin.h> // For _mm_extract_epi64, _mm_insert_epi64 (SSE4.1)
 
 // Include the reduction function from gf128_pclmul.c
 // NOTE: This requires gf128_reduce_pclmul to be declared static inline
 // in a shared header or duplicated here. For simplicity, let's assume
 // it's available via a shared internal header or direct inclusion/duplication.
 // We'll duplicate the reduction function here for now.
 
 // Optimized reduction using PCLMUL (duplicated from gf128_pclmul.c)
 static inline __m128i gf128_reduce_pclmul_kara(__m128i lo128, __m128i hi128) {
     // Precomputed reduction constant based on polynomial P(x)=x^128+x^7+x^2+x+1 (0x87)
     const __m128i poly_const = _mm_set_epi64x(0x1, 0xc200000000000000); // Constant derived for GCM reduction
 
     __m128i tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
 
     // Step 1: Calculate Tmp = Hi[63:0] * P_const[63:0]
     tmp1 = _mm_clmulepi64_si128(hi128, poly_const, 0x01); // hi128[63:0] * poly_const[63:0]
 
     // Step 2: Tmp = Tmp XOR Hi[127:64]
     tmp2 = _mm_shuffle_epi32(hi128, _MM_SHUFFLE(1, 0, 3, 2)); // Swap hi/lo 64-bit parts of hi128
     tmp3 = _mm_xor_si128(tmp1, tmp2); // XOR with hi128[127:64]
 
     // Step 3: Tmp = Tmp[63:0] * P_const[63:0]
     tmp4 = _mm_clmulepi64_si128(tmp3, poly_const, 0x00); // tmp3[63:0] * poly_const[63:0]
 
     // Step 4: Result = Tmp XOR Tmp[127:64] XOR Lo[127:64] XOR Lo[63:0]
     tmp5 = _mm_shuffle_epi32(tmp3, _MM_SHUFFLE(1, 0, 3, 2)); // Swap hi/lo 64-bit parts of tmp3
     tmp6 = _mm_xor_si128(_mm_xor_si128(tmp4, tmp5), lo128); // Final reduction result
 
     return tmp6;
 }
 
 
 // PCLMUL Karatsuba multiplication (3 CLMULs)
 gf128_t gf128_mul_pclmul_kara(gf128_t a, gf128_t b) {
     __m128i x = _mm_set_epi64x((long long)a.hi, (long long)a.lo);
     __m128i y = _mm_set_epi64x((long long)b.hi, (long long)b.lo);
 
     // Karatsuba multiplication:
     // a = a1*x^64 + a0
     // b = b1*x^64 + b0
     // a*b = (a1*b1)*x^128 + ((a1+a0)*(b1+b0) - a1*b1 - a0*b0)*x^64 + (a0*b0)
 
     // Calculate the three products:
     // d0 = a0 * b0
     __m128i d0 = _mm_clmulepi64_si128(x, y, 0x00); // a.lo * b.lo
 
     // d2 = a1 * b1
     __m128i d2 = _mm_clmulepi64_si128(x, y, 0x11); // a.hi * b.hi
 
     // Calculate (a1+a0) and (b1+b0). In GF(2), addition is XOR.
     // Extract a.hi and b.hi efficiently. SSE4.1 needed for _mm_extract_epi64.
     // A potentially more compatible way without SSE4.1 for extract:
     __m128i x_hi_in_lo = _mm_srli_si128(x, 8);
     __m128i y_hi_in_lo = _mm_srli_si128(y, 8);
     __m128i a1_xor_a0 = _mm_xor_si128(x, x_hi_in_lo); // (a.hi ^ a.lo) potentially in lower 64 bits
     __m128i b1_xor_b0 = _mm_xor_si128(y, y_hi_in_lo); // (b.hi ^ b.lo) potentially in lower 64 bits
 
     // d1_term = (a1+a0) * (b1+b0)
     // We only need the lower 64 bits of a1_xor_a0 and b1_xor_b0 for the clmul
     __m128i d1_term = _mm_clmulepi64_si128(a1_xor_a0, b1_xor_b0, 0x00);
 
     // d1 = d1_term - d2 - d0 (subtraction is XOR in GF(2))
     __m128i d1 = _mm_xor_si128(_mm_xor_si128(d1_term, d2), d0);
 
     // Combine the terms: result = d2 * x^128 + d1 * x^64 + d0
    // Product(256) = [d2_hi | d2_lo | 0 | 0 ]  ^
    //                [ 0 | d1_hi | d1_lo | 0 ]  ^
    //                [ 0 | 0 | d0_hi | d0_lo ]
     // Construct the 256-bit result (lo128, hi128) before reduction
    // Calculate lo128 = [d0_hi ^ d1_lo | d0_lo]
    __m128i d1_lo_shifted = _mm_slli_si128(d1, 8); // Creates [d1_lo | 0]
    __m128i lo128 = _mm_xor_si128(d0, d1_lo_shifted); // d0 ^ [d1_lo | 0] = [d0_hi^d1_lo | d0_lo]
 
    // Calculate hi128 = [d2_hi | d2_lo ^ d1_hi]
    __m128i d1_hi_shifted = _mm_srli_si128(d1, 8); // Creates [0 | d1_hi]
    __m128i hi128 = _mm_xor_si128(d2, d1_hi_shifted); // d2 ^ [0 | d1_hi] = [d2_hi | d2_lo ^ d1_hi]
 
     // Reduce the 256-bit result
     __m128i result_vec = gf128_reduce_pclmul_kara(lo128, hi128);
 
     // Store result back to gf128_t struct
     gf128_t result;
    _mm_storeu_si128((__m128i*)&result, result_vec);
    return result;
}
