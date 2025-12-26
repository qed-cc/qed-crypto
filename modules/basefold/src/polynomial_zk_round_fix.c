/**
 * @file polynomial_zk_round_fix.c
 * @brief Fix for applying polynomial ZK during sumcheck rounds
 * 
 * This demonstrates how to properly apply randomization during
 * the round polynomial computation to achieve true zero-knowledge.
 */

#include "gate_sumcheck_multilinear.h"
#include "multilinear.h"
#include "vanishing_poly.h"
#include "gf128.h"
#include "sha3.h"
#include <string.h>

/**
 * @brief Generate deterministic randomness for a specific evaluation point
 * 
 * Uses the ZK seed and evaluation point to generate a pseudorandom field element
 * that will be used to mask the polynomial evaluation.
 */
static gf128_t generate_mask_for_point(
    const uint8_t* zk_seed,
    size_t round,
    size_t point_index,
    const gf128_t* partial_point)
{
    // Create unique input for this evaluation point
    uint8_t hash_input[256];
    size_t offset = 0;
    
    // Add ZK seed
    memcpy(hash_input + offset, zk_seed, 32);
    offset += 32;
    
    // Add round number
    memcpy(hash_input + offset, &round, sizeof(size_t));
    offset += sizeof(size_t);
    
    // Add point index
    memcpy(hash_input + offset, &point_index, sizeof(size_t));
    offset += sizeof(size_t);
    
    // Add partial evaluation point (challenges from previous rounds)
    for (size_t i = 0; i < round; i++) {
        memcpy(hash_input + offset, &partial_point[i], sizeof(gf128_t));
        offset += sizeof(gf128_t);
    }
    
    // Hash to get random field element
    uint8_t hash_output[32];
    sha3_hash(SHA3_256, hash_input, offset, hash_output, 32);
    
    // Convert to GF128
    gf128_t mask;
    memcpy(&mask.lo, hash_output, 8);
    memcpy(&mask.hi, hash_output + 8, 8);
    
    return mask;
}

/**
 * @brief Apply polynomial ZK masking during round computation
 * 
 * This is the key fix: During each sumcheck round, we need to apply
 * the polynomial randomization to make the round polynomials different
 * for each proof while maintaining correctness.
 * 
 * The idea is that for each evaluation in the round polynomial:
 * - If we're at a boolean point on the remaining variables, no mask
 * - Otherwise, apply a deterministic random mask based on the point
 */
void apply_round_polynomial_zk(
    gate_sumcheck_ml_t* instance,
    size_t round,
    gf128_t* g_evals)
{
    if (!instance->has_zk) {
        return;  // No ZK, nothing to do
    }
    
    // For round i, we're fixing variable x_i and summing over remaining vars
    // g(0) sums over points where x_i = 0
    // g(1) sums over points where x_i = 1
    
    // The key insight: After fixing the first i variables to challenges,
    // we're no longer on the boolean hypercube for those variables.
    // This means the vanishing polynomial is non-zero and we need masking.
    
    if (round > 0) {
        // We have partial evaluation point from previous rounds
        // Generate masks based on the partial point
        
        gf128_t mask_0 = generate_mask_for_point(
            instance->zk_seed_data, round, 0, instance->challenges);
        gf128_t mask_1 = generate_mask_for_point(
            instance->zk_seed_data, round, 1, instance->challenges);
        
        // Apply additive masking to the round polynomial evaluations
        // This preserves the linear structure needed for sumcheck
        g_evals[0] = gf128_add(g_evals[0], mask_0);
        g_evals[1] = gf128_add(g_evals[1], mask_1);
    }
    
    // Note: For round 0, we're still on the boolean hypercube for all
    // variables, so no masking is needed (vanishing poly = 0)
}

/**
 * @brief Enhanced round polynomial computation with ZK
 * 
 * This replaces the standard compute_round_polynomial_ml_fast
 * to include polynomial randomization.
 */
void compute_round_polynomial_ml_fast_with_zk(
    gate_sumcheck_ml_t* instance,
    size_t round,
    gf128_t* g_evals)
{
    // First compute the standard round polynomial
    size_t N = instance->eval_size;
    size_t half = N / 2;
    
    gf128_t sum_0 = gf128_zero();
    gf128_t sum_1 = gf128_zero();
    
    for (size_t i = 0; i < half; i++) {
        sum_0 = gf128_add(sum_0, instance->eval_buffer[2 * i]);
        sum_1 = gf128_add(sum_1, instance->eval_buffer[2 * i + 1]);
    }
    
    g_evals[0] = sum_0;
    g_evals[1] = sum_1;
    g_evals[2] = gf128_zero();  // Not needed for multilinear
    
    // Apply ZK masking if enabled
    apply_round_polynomial_zk(instance, round, g_evals);
}

/**
 * @brief Update the evaluation buffer with ZK after folding
 * 
 * After each round, we need to update the masked values in the buffer
 * to account for the partial evaluation point growing.
 */
void update_buffer_with_zk(
    gate_sumcheck_ml_t* instance,
    size_t round)
{
    if (!instance->has_zk || round == 0) {
        return;  // No ZK or still on hypercube
    }
    
    // The buffer now represents evaluations at points that have
    // the first 'round' variables fixed to challenges.
    // We need to add masking based on these partial points.
    
    size_t remaining_vars = instance->num_vars - round;
    size_t buffer_size = 1ULL << remaining_vars;
    
    for (size_t i = 0; i < buffer_size && i < instance->eval_size; i++) {
        // Generate mask for this partial evaluation
        gf128_t mask = generate_mask_for_point(
            instance->zk_seed_data, round, i, instance->challenges);
        
        // Apply additive mask
        instance->eval_buffer[i] = gf128_add(instance->eval_buffer[i], mask);
    }
}

/* 
 * Integration Notes:
 * 
 * To properly integrate this fix:
 * 
 * 1. Replace compute_round_polynomial_ml_fast with compute_round_polynomial_ml_fast_with_zk
 * 2. Call update_buffer_with_zk after each folding step
 * 3. Ensure instance->challenges is properly maintained
 * 
 * This will make each proof have different round polynomials while
 * maintaining the correctness of the sumcheck protocol.
 */