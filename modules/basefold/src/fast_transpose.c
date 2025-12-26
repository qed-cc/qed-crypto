/**
 * @file fast_transpose.c
 * @brief Ultra-fast AVX-512 matrix transpose for sumcheck
 */

#include <immintrin.h>
#include <string.h>
#include <stdlib.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef struct {
    uint64_t lo;
    uint64_t hi;
} gf128_t;

// Transpose 4x4 block of __m128i elements using AVX-512
static inline void transpose_4x4_block_avx512(
    const __m128i* src, 
    gf128_t* dst_L,
    gf128_t* dst_R, 
    gf128_t* dst_O,
    gf128_t* dst_S,
    size_t gate_idx)
{
    // Load 16 __m128i elements (4 gates x 4 wires)
    __m512i row0 = _mm512_loadu_si512(&src[0]);  // L0,R0,O0,S0
    __m512i row1 = _mm512_loadu_si512(&src[4]);  // L1,R1,O1,S1
    __m512i row2 = _mm512_loadu_si512(&src[8]);  // L2,R2,O2,S2
    __m512i row3 = _mm512_loadu_si512(&src[12]); // L3,R3,O3,S3
    
    // Extract L values (indices 0,4,8,12)
    __m512i idx_L = _mm512_set_epi64(12, 8, 4, 0, 12, 8, 4, 0);
    __m512i L_vals = _mm512_permutex2var_epi64(row0, idx_L, row2);
    
    // Extract R values (indices 1,5,9,13)
    __m512i idx_R = _mm512_set_epi64(13, 9, 5, 1, 13, 9, 5, 1);
    __m512i R_vals = _mm512_permutex2var_epi64(row0, idx_R, row2);
    
    // Extract O values (indices 2,6,10,14)
    __m512i idx_O = _mm512_set_epi64(14, 10, 6, 2, 14, 10, 6, 2);
    __m512i O_vals = _mm512_permutex2var_epi64(row1, idx_O, row3);
    
    // Extract S values (indices 3,7,11,15)
    __m512i idx_S = _mm512_set_epi64(15, 11, 7, 3, 15, 11, 7, 3);
    __m512i S_vals = _mm512_permutex2var_epi64(row1, idx_S, row3);
    
    // Store transposed values
    _mm512_storeu_si512(&dst_L[gate_idx], L_vals);
    _mm512_storeu_si512(&dst_R[gate_idx], R_vals);
    _mm512_storeu_si512(&dst_O[gate_idx], O_vals);
    _mm512_storeu_si512(&dst_S[gate_idx], S_vals);
}

// Fast parallel transpose using all available cores
void fast_transpose_gate_data(
    const __m128i* src,      // Row-major: [L0,R0,O0,S0, L1,R1,O1,S1, ...]
    gf128_t* dst,            // Column-major: [L0,L1,...,Ln, R0,R1,...,Rn, ...]
    size_t num_gates)
{
    // Pointers to each wire's section in output
    gf128_t* dst_L = dst;
    gf128_t* dst_R = dst + num_gates;
    gf128_t* dst_O = dst + 2 * num_gates;
    gf128_t* dst_S = dst + 3 * num_gates;
    
    #pragma omp parallel for schedule(static)
    for (size_t i = 0; i < num_gates; i++) {
        // Direct extraction from __m128i to gf128_t
        __m128i L_m128 = src[i * 4 + 0];
        __m128i R_m128 = src[i * 4 + 1];
        __m128i O_m128 = src[i * 4 + 2];
        __m128i S_m128 = src[i * 4 + 3];
        
        // Store directly using aligned stores if possible
        _mm_storeu_si128((__m128i*)&dst_L[i], L_m128);
        _mm_storeu_si128((__m128i*)&dst_R[i], R_m128);
        _mm_storeu_si128((__m128i*)&dst_O[i], O_m128);
        _mm_storeu_si128((__m128i*)&dst_S[i], S_m128);
    }
}

// Even faster: avoid transpose entirely by working with row-major data
void setup_multilinear_rowmajor(
    const __m128i* field_elements,  // Row-major data
    size_t num_gates,
    void* ml_instance)              // Multilinear instance to setup
{
    // TODO: Modify multilinear polynomials to work with row-major data
    // This would eliminate the transpose entirely!
}