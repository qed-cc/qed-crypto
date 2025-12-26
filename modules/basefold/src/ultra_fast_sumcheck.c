/**
 * @file ultra_fast_sumcheck.c
 * @brief Ultra-fast sumcheck that works directly with trace field elements
 */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <immintrin.h>
#include "transcript.h"
#include "gf128.h"
#include "merkle/build.h"

typedef struct {
    __m128i* field_elements;  // Direct pointer to trace data
    size_t num_gates;
    size_t num_rounds;
    transcript_t* transcript;
    merkle_tree_t* tree;
    uint8_t* coeffs_out;
    uint8_t zk_seed[16];
    int has_zk;
} ultra_fast_sumcheck_t;

// Compute gate constraint: S*(L*R) + (1-S)*(L+R+O)
static inline gf128_t compute_gate_constraint(
    gf128_t L, gf128_t R, gf128_t O, gf128_t S)
{
    gf128_t lr = gf128_mul(L, R);
    gf128_t lro = gf128_add(gf128_add(L, R), O);
    gf128_t one_minus_s = gf128_add(gf128_one(), S);
    
    gf128_t term1 = gf128_mul(S, lr);
    gf128_t term2 = gf128_mul(one_minus_s, lro);
    
    return gf128_add(term1, term2);
}

// Ultra-fast sumcheck round using AVX-512
static void ultra_fast_round(
    ultra_fast_sumcheck_t* ctx,
    size_t round,
    size_t current_gates,
    gf128_t* g_evals)
{
    gf128_t sum_0 = gf128_zero();
    gf128_t sum_1 = gf128_zero();
    
    size_t half = current_gates / 2;
    
    // For first round, compute gate constraints
    if (round == 0) {
        // Process gates in parallel
        #pragma omp parallel reduction(gf128_add:sum_0,sum_1)
        {
            gf128_t local_sum_0 = gf128_zero();
            gf128_t local_sum_1 = gf128_zero();
            
            #pragma omp for schedule(static, 256)
            for (size_t i = 0; i < half; i++) {
                // Even gate (x_0 = 0)
                size_t idx_even = i * 2;
                __m128i* gate_even = &ctx->field_elements[idx_even * 4];
                
                gf128_t L_even, R_even, O_even, S_even;
                _mm_storeu_si128((__m128i*)&L_even, gate_even[0]);
                _mm_storeu_si128((__m128i*)&R_even, gate_even[1]);
                _mm_storeu_si128((__m128i*)&O_even, gate_even[2]);
                _mm_storeu_si128((__m128i*)&S_even, gate_even[3]);
                
                local_sum_0 = gf128_add(local_sum_0, 
                    compute_gate_constraint(L_even, R_even, O_even, S_even));
                
                // Odd gate (x_0 = 1)
                size_t idx_odd = i * 2 + 1;
                __m128i* gate_odd = &ctx->field_elements[idx_odd * 4];
                
                gf128_t L_odd, R_odd, O_odd, S_odd;
                _mm_storeu_si128((__m128i*)&L_odd, gate_odd[0]);
                _mm_storeu_si128((__m128i*)&R_odd, gate_odd[1]);
                _mm_storeu_si128((__m128i*)&O_odd, gate_odd[2]);
                _mm_storeu_si128((__m128i*)&S_odd, gate_odd[3]);
                
                local_sum_1 = gf128_add(local_sum_1,
                    compute_gate_constraint(L_odd, R_odd, O_odd, S_odd));
            }
            
            sum_0 = gf128_add(sum_0, local_sum_0);
            sum_1 = gf128_add(sum_1, local_sum_1);
        }
    } else {
        // For later rounds, just sum the folded values
        // TODO: Implement folded sum
    }
    
    g_evals[0] = sum_0;
    g_evals[1] = sum_1;
    g_evals[2] = gf128_zero();
}

// Run complete sumcheck protocol
int ultra_fast_sumcheck_prove(
    __m128i* field_elements,
    size_t num_gates,
    transcript_t* transcript,
    merkle_tree_t* tree,
    uint8_t* coeffs_out,
    const uint8_t* zk_seed)
{
    ultra_fast_sumcheck_t ctx = {
        .field_elements = field_elements,
        .num_gates = num_gates,
        .transcript = transcript,
        .tree = tree,
        .coeffs_out = coeffs_out,
        .has_zk = (zk_seed != NULL)
    };
    
    if (zk_seed) {
        memcpy(ctx.zk_seed, zk_seed, 16);
    }
    
    // Calculate number of rounds
    ctx.num_rounds = 0;
    size_t temp = num_gates;
    while (temp > 1) {
        temp >>= 1;
        ctx.num_rounds++;
    }
    
    size_t current_gates = num_gates;
    
    // Run rounds
    for (size_t round = 0; round < ctx.num_rounds; round++) {
        gf128_t g_evals[3];
        
        // Compute round polynomial
        ultra_fast_round(&ctx, round, current_gates, g_evals);
        
        // Store coefficients
        memcpy(coeffs_out + round * 64, &g_evals[0], 16);
        memcpy(coeffs_out + round * 64 + 16, &g_evals[1], 16);
        memcpy(coeffs_out + round * 64 + 32, &g_evals[2], 16);
        memset(coeffs_out + round * 64 + 48, 0, 16);
        
        // Send to transcript
        uint8_t coeffs_bytes[48];
        memcpy(coeffs_bytes, &g_evals[0], 16);
        memcpy(coeffs_bytes + 16, &g_evals[1], 16);
        memcpy(coeffs_bytes + 32, &g_evals[2], 16);
        fs_absorb(transcript, coeffs_bytes, 48);
        
        // Get challenge
        uint8_t challenge_bytes[32];
        fs_challenge(transcript, challenge_bytes);
        gf128_t challenge = gf128_from_bytes(challenge_bytes);
        
        // TODO: Fold for next round
        current_gates /= 2;
        
        if ((round % 5) == 0) {
            printf("Ultra-fast sumcheck round %zu/%zu\n", round, ctx.num_rounds);
        }
    }
    
    return 0;
}