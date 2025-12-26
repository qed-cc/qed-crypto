/**
 * @file direct_sumcheck.c
 * @brief Direct sumcheck that works with row-major data - no transpose needed!
 */

#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "gate_sumcheck_multilinear.h"
#include "multilinear.h"
#include "gf128.h"
#include "transcript.h"

// Direct initialization from row-major field elements
int direct_sumcheck_init(
    gate_sumcheck_ml_t* instance,
    const __m128i* field_elements,  // Row-major: [L0,R0,O0,S0, L1,R1,O1,S1, ...]
    size_t num_gates,
    size_t num_vars)
{
    instance->num_vars = num_vars;
    instance->eval_size = num_gates * 4;  // Start with all 4 wires
    instance->has_zk = 0;
    instance->current_round = 0;
    
    // Allocate evaluation buffer for first round
    instance->eval_buffer = aligned_alloc(64, instance->eval_size * sizeof(gf128_t));
    if (!instance->eval_buffer) return -1;
    
    // Copy field elements directly - no transpose!
    memcpy(instance->eval_buffer, field_elements, instance->eval_size * sizeof(gf128_t));
    
    instance->challenges = calloc(num_vars, sizeof(gf128_t));
    if (!instance->challenges) {
        free(instance->eval_buffer);
        return -1;
    }
    
    return 0;
}

// Compute round polynomial directly from row-major data
void compute_round_poly_rowmajor(
    const gf128_t* buffer,  // [L0,R0,O0,S0, L1,R1,O1,S1, ...]
    size_t num_gates,
    gf128_t* g_evals)
{
    gf128_t sum_0 = gf128_zero();
    gf128_t sum_1 = gf128_zero();
    
    // For first round, we sum over gate constraint polynomials
    // g(b) = sum over i where x_0 = b of: S_i * (L_i * R_i) + (1-S_i) * (L_i + R_i + O_i)
    
    size_t half = num_gates / 2;
    
    // Process gates where x_0 = 0 (even indices)
    for (size_t i = 0; i < half; i++) {
        size_t idx = i * 2;  // Even gate index
        const gf128_t* gate = &buffer[idx * 4];
        
        gf128_t L = gate[0];
        gf128_t R = gate[1];
        gf128_t O = gate[2];
        gf128_t S = gate[3];
        
        // Compute gate constraint
        gf128_t lr = gf128_mul(L, R);
        gf128_t lro = gf128_add(gf128_add(L, R), O);
        gf128_t one_minus_s = gf128_add(gf128_one(), S);
        
        gf128_t term1 = gf128_mul(S, lr);
        gf128_t term2 = gf128_mul(one_minus_s, lro);
        
        sum_0 = gf128_add(sum_0, gf128_add(term1, term2));
    }
    
    // Process gates where x_0 = 1 (odd indices)
    for (size_t i = 0; i < half; i++) {
        size_t idx = i * 2 + 1;  // Odd gate index
        const gf128_t* gate = &buffer[idx * 4];
        
        gf128_t L = gate[0];
        gf128_t R = gate[1];
        gf128_t O = gate[2];
        gf128_t S = gate[3];
        
        // Compute gate constraint
        gf128_t lr = gf128_mul(L, R);
        gf128_t lro = gf128_add(gf128_add(L, R), O);
        gf128_t one_minus_s = gf128_add(gf128_one(), S);
        
        gf128_t term1 = gf128_mul(S, lr);
        gf128_t term2 = gf128_mul(one_minus_s, lro);
        
        sum_1 = gf128_add(sum_1, gf128_add(term1, term2));
    }
    
    g_evals[0] = sum_0;
    g_evals[1] = sum_1;
    g_evals[2] = gf128_zero(); // Linear polynomial
}

// Fold buffer after receiving challenge - row major version
void fold_rowmajor_buffer(
    gf128_t* buffer,
    size_t num_gates,
    gf128_t challenge)
{
    gf128_t one_minus_r = gf128_add(gf128_one(), challenge);
    size_t new_num_gates = num_gates / 2;
    
    // Fold gates: new[i] = (1-r)*even[i] + r*odd[i]
    for (size_t i = 0; i < new_num_gates; i++) {
        const gf128_t* even_gate = &buffer[(i * 2) * 4];
        const gf128_t* odd_gate = &buffer[(i * 2 + 1) * 4];
        gf128_t* new_gate = &buffer[i * 4];
        
        // Fold each wire
        for (int w = 0; w < 4; w++) {
            gf128_t even_val = even_gate[w];
            gf128_t odd_val = odd_gate[w];
            
            gf128_t t0 = gf128_mul(one_minus_r, even_val);
            gf128_t t1 = gf128_mul(challenge, odd_val);
            
            new_gate[w] = gf128_add(t0, t1);
        }
    }
}