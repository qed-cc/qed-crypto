/**
 * @file gate_sumcheck_avx512_simple.c
 * @brief Simple, correct AVX-512 implementation for sumcheck
 */

#include <immintrin.h>
#include <stdint.h>

typedef struct {
    uint64_t lo;
    uint64_t hi;
} gf128_t;

static inline gf128_t gf128_zero(void) {
    gf128_t r = {0, 0};
    return r;
}

static inline gf128_t gf128_add(gf128_t a, gf128_t b) {
    gf128_t r;
    r.lo = a.lo ^ b.lo;
    r.hi = a.hi ^ b.hi;
    return r;
}

// Simple AVX-512 sum of even/odd pairs
void gf128_sum_pairs_avx512_simple(
    gf128_t* sum_even, 
    gf128_t* sum_odd,
    const gf128_t* buffer, 
    size_t num_pairs)
{
    __m512i acc_even = _mm512_setzero_si512();
    __m512i acc_odd = _mm512_setzero_si512();
    
    size_t i = 0;
    
    // Process 4 pairs at a time (8 GF128 elements = 128 bytes = 1 cache line)
    for (; i + 3 < num_pairs; i += 4) {
        // Load 8 GF128 elements (4 pairs)
        // buffer[0] = even0, buffer[1] = odd0, buffer[2] = even1, buffer[3] = odd1, etc.
        __m512i data = _mm512_loadu_si512(&buffer[2*i]);
        
        // Extract even elements (positions 0, 2, 4, 6)
        // We'll use shuffle to rearrange
        // Want: [even0, even1, even2, even3, ?, ?, ?, ?]
        __m512i idx_even = _mm512_set_epi64(7, 6, 5, 4, 6, 4, 2, 0);
        __m512i even = _mm512_permutexvar_epi64(idx_even, data);
        
        // Extract odd elements (positions 1, 3, 5, 7)
        // Want: [odd0, odd1, odd2, odd3, ?, ?, ?, ?]
        __m512i idx_odd = _mm512_set_epi64(7, 6, 5, 4, 7, 5, 3, 1);
        __m512i odd = _mm512_permutexvar_epi64(idx_odd, data);
        
        // Accumulate (only lower 4 elements matter)
        acc_even = _mm512_xor_si512(acc_even, even);
        acc_odd = _mm512_xor_si512(acc_odd, odd);
    }
    
    // Reduce accumulator to scalar
    // We only used the lower 256 bits of each accumulator
    __m256i acc_even_low = _mm512_extracti64x4_epi64(acc_even, 0);
    __m256i acc_odd_low = _mm512_extracti64x4_epi64(acc_odd, 0);
    
    // Extract individual GF128 values and sum
    gf128_t temp[4];
    _mm256_storeu_si256((__m256i*)temp, acc_even_low);
    *sum_even = gf128_add(*sum_even, gf128_add(temp[0], gf128_add(temp[1], gf128_add(temp[2], temp[3]))));
    
    _mm256_storeu_si256((__m256i*)temp, acc_odd_low);
    *sum_odd = gf128_add(*sum_odd, gf128_add(temp[0], gf128_add(temp[1], gf128_add(temp[2], temp[3]))));
    
    // Handle remaining pairs with scalar code
    for (; i < num_pairs; i++) {
        *sum_even = gf128_add(*sum_even, buffer[2*i]);
        *sum_odd = gf128_add(*sum_odd, buffer[2*i + 1]);
    }
}