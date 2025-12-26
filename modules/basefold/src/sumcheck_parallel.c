/**
 * @file sumcheck_parallel.c
 * @brief Parallel implementation of sumcheck folding
 */

#include <omp.h>
#include <string.h>
#include "gate_sumcheck_multilinear.h"

void fold_eval_buffer_parallel(gate_sumcheck_ml_t* instance, gf128_t challenge) {
    size_t N = instance->eval_size;
    size_t half = N / 2;
    
    gf128_t one_minus_r = gf128_add(gf128_one(), challenge);
    
    // Allocate new buffer
    gf128_t* new_buffer = malloc(half * sizeof(gf128_t));
    if (!new_buffer) return;
    
    // Parallel folding using OpenMP
    #pragma omp parallel for schedule(static)
    for (size_t i = 0; i < half; i++) {
        gf128_t even_val = instance->eval_buffer[2 * i];
        gf128_t odd_val = instance->eval_buffer[2 * i + 1];
        
        // Thread-local multiplication
        gf128_t t0 = gf128_mul(one_minus_r, even_val);
        gf128_t t1 = gf128_mul(challenge, odd_val);
        
        new_buffer[i] = gf128_add(t0, t1);
    }
    
    // Replace old buffer
    free(instance->eval_buffer);
    instance->eval_buffer = new_buffer;
    instance->eval_size = half;
}

void compute_round_polynomial_parallel(
    gate_sumcheck_ml_t* instance, 
    size_t round, 
    gf128_t* g_evals) 
{
    size_t half = instance->eval_size / 2;
    
    // Use atomic operations for accumulation
    __int128 sum_0_atomic = 0;
    __int128 sum_1_atomic = 0;
    
    #pragma omp parallel for reduction(+:sum_0_atomic,sum_1_atomic)
    for (size_t i = 0; i < half; i++) {
        gf128_t p_0 = instance->eval_buffer[2 * i];
        gf128_t p_1 = instance->eval_buffer[2 * i + 1];
        
        // Accumulate locally
        sum_0_atomic += *((__int128*)&p_0);
        sum_1_atomic += *((__int128*)&p_1);
    }
    
    // Convert back to gf128_t
    g_evals[0] = *(gf128_t*)&sum_0_atomic;
    g_evals[1] = *(gf128_t*)&sum_1_atomic;
    g_evals[2] = gf128_zero();
}