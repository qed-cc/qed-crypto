/**
 * @file gate_sumcheck_multilinear.c
 * @brief Multilinear polynomial SumCheck implementation for gate constraints
 */

#include "gate_sumcheck_multilinear.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* Helper to create gf128 from int */
static inline gf128_t gf128_from_int(int x) {
    gf128_t result = {0, (uint64_t)x};
    return result;
}

/* Core evaluation function */

gf128_t gate_constraint_ml_eval(
    const gate_sumcheck_instance_t* instance,
    const gf128_t* point) {
    
    if (!instance || !point) return gf128_zero();
    
    // Evaluate each polynomial at the point
    gf128_t l_val = multilinear_eval(instance->L, point);
    gf128_t r_val = multilinear_eval(instance->R, point);
    gf128_t o_val = multilinear_eval(instance->O, point);
    gf128_t s_val = multilinear_eval(instance->S, point);
    
    // Compute F(point) = S(point)·(L(point)·R(point)) + (1-S(point))·(L(point)+R(point)) - O(point)
    
    // AND part: S·(L·R)
    gf128_t lr_product = gf128_mul(l_val, r_val);
    gf128_t and_part = gf128_mul(s_val, lr_product);
    
    // XOR part: (1-S)·(L+R)
    gf128_t one_minus_s = gf128_add(gf128_one(), s_val);  // In GF(2^128), -1 = 1
    gf128_t l_plus_r = gf128_add(l_val, r_val);
    gf128_t xor_part = gf128_mul(one_minus_s, l_plus_r);
    
    // Combine: S·(L·R) + (1-S)·(L+R) - O
    gf128_t result = gf128_add(and_part, xor_part);
    result = gf128_add(result, o_val);  // In GF(2^128), -O = O
    
    return result;
}

/* Round polynomial computation */

void compute_round_polynomial_ml(
    gate_sumcheck_instance_t* instance,
    size_t round,
    const gf128_t* challenges,
    round_polynomial_t* round_poly) {
    
    if (!instance || !round_poly) return;
    
    size_t num_vars = instance->num_vars;
    
    // Initialize polynomial coefficients to zero
    memset(round_poly->coeffs, 0, sizeof(round_poly->coeffs));
    
    // Special case for no variables
    if (num_vars == 0) {
        round_poly->degree = 0;
        return;
    }
    
    size_t num_remaining = num_vars - round;
    size_t num_points = 1ULL << (num_remaining - 1);
    
    // Debug output for large computations
    if (num_points > 10000) {
        printf("WARNING: Round %zu will evaluate %zu points (2^%zu)\n", 
               round, num_points, num_remaining - 1);
    }
    
    // The univariate polynomial g_i(X) has degree at most 2
    round_poly->degree = 2;
    
    // We'll compute g_i(X) = sum over x_{i+1},...,x_n of F(r_1,...,r_{i-1},X,x_{i+1},...,x_n)
    // Since F has degree at most 2 in X, we need g(0), g(1), g(2) to interpolate
    
    gf128_t sum_at_0 = gf128_zero();
    gf128_t sum_at_1 = gf128_zero();
    gf128_t sum_at_2 = gf128_zero();
    
    // For each assignment to the remaining variables
    for (size_t j = 0; j < num_points; j++) {
        // Build evaluation point
        gf128_t point[num_vars];
        
        // First 'round' variables are fixed to challenges
        for (size_t k = 0; k < round; k++) {
            point[k] = challenges[k];
        }
        
        // Remaining variables from binary expansion of j
        for (size_t k = round + 1; k < num_vars; k++) {
            size_t bit_idx = k - round - 1;
            point[k] = (j & (1ULL << bit_idx)) ? gf128_one() : gf128_zero();
        }
        
        // Evaluate at X_round = 0
        point[round] = gf128_zero();
        sum_at_0 = gf128_add(sum_at_0, gate_constraint_ml_eval(instance, point));
        
        // Evaluate at X_round = 1
        point[round] = gf128_one();
        sum_at_1 = gf128_add(sum_at_1, gate_constraint_ml_eval(instance, point));
        
        // Evaluate at X_round = 2
        point[round] = gf128_from_int(2);
        sum_at_2 = gf128_add(sum_at_2, gate_constraint_ml_eval(instance, point));
    }
    
    // Now we have g(0) = sum_at_0, g(1) = sum_at_1, g(2) = sum_at_2
    // We need to find coefficients c0, c1, c2 such that:
    // g(X) = c0 + c1*X + c2*X^2
    
    // Using Lagrange interpolation for points (0,sum_at_0), (1,sum_at_1), (2,sum_at_2)
    // In GF(2^128), we can use the fact that 2 = alpha where alpha is a field element
    
    // For simplicity, let's use the direct approach:
    // c0 = g(0) = sum_at_0
    // c0 + c1 + c2 = g(1) = sum_at_1
    // c0 + 2*c1 + 4*c2 = g(2) = sum_at_2
    
    round_poly->coeffs[0] = sum_at_0;
    
    // c1 + c2 = sum_at_1 - sum_at_0
    gf128_t c1_plus_c2 = gf128_add(sum_at_1, sum_at_0);
    
    // 2*c1 + 4*c2 = sum_at_2 - sum_at_0
    gf128_t two_c1_plus_four_c2 = gf128_add(sum_at_2, sum_at_0);
    
    // Solve for c1 and c2
    // From first: c1 = c1_plus_c2 - c2
    // Substitute into second: 2*(c1_plus_c2 - c2) + 4*c2 = two_c1_plus_four_c2
    // 2*c1_plus_c2 - 2*c2 + 4*c2 = two_c1_plus_four_c2
    // 2*c1_plus_c2 + 2*c2 = two_c1_plus_four_c2
    // 2*c2 = two_c1_plus_four_c2 - 2*c1_plus_c2
    
    gf128_t two = gf128_from_int(2);
    gf128_t two_c1_plus_c2 = gf128_mul(two, c1_plus_c2);
    gf128_t two_c2 = gf128_add(two_c1_plus_four_c2, two_c1_plus_c2);
    
    // c2 = two_c2 / 2
    gf128_t two_inv = gf128_inv(two);
    round_poly->coeffs[2] = gf128_mul(two_c2, two_inv);
    
    // c1 = c1_plus_c2 - c2
    round_poly->coeffs[1] = gf128_add(c1_plus_c2, round_poly->coeffs[2]);
}

/* Prover implementation */

void gate_sc_ml_prover_init(
    gate_sc_ml_prover_t* prover,
    gate_sumcheck_instance_t* instance,
    fiat_shamir_t* transcript) {
    
    if (!prover || !instance || !transcript) return;
    
    prover->instance = instance;
    prover->transcript = transcript;
    prover->current_round = 0;
    
    // Allocate space for challenges
    prover->challenges = calloc(instance->num_vars, sizeof(gf128_t));
    
    // Initialize memoization tables for efficiency
    prover->memo_L = multilinear_memo_create(instance->num_vars);
    prover->memo_R = multilinear_memo_create(instance->num_vars);
    prover->memo_O = multilinear_memo_create(instance->num_vars);
    prover->memo_S = multilinear_memo_create(instance->num_vars);
}

bool gate_sc_ml_prover_round(
    gate_sc_ml_prover_t* prover,
    round_polynomial_t* round_poly) {
    
    if (!prover || !round_poly) return false;
    if (prover->current_round >= prover->instance->num_vars) return false;
    
    // Compute round polynomial
    compute_round_polynomial_ml(
        prover->instance,
        prover->current_round,
        prover->challenges,
        round_poly
    );
    
    // Add polynomial to transcript
    fs_absorb(prover->transcript, 
              round_poly->coeffs, 
              sizeof(round_poly->coeffs));
    
    // Get challenge for this round
    uint8_t challenge_bytes[32];
    fs_challenge(prover->transcript, challenge_bytes);
    // Use first 16 bytes as GF(128) element
    memcpy(&prover->challenges[prover->current_round], challenge_bytes, sizeof(gf128_t));
    
    prover->current_round++;
    return true;
}

void gate_sc_ml_prover_final(
    gate_sc_ml_prover_t* prover,
    gf128_t evals[4]) {
    
    if (!prover || !evals) return;
    
    // Evaluate all polynomials at the final point
    evals[0] = multilinear_eval(prover->instance->L, prover->challenges);
    evals[1] = multilinear_eval(prover->instance->R, prover->challenges);
    evals[2] = multilinear_eval(prover->instance->O, prover->challenges);
    evals[3] = multilinear_eval(prover->instance->S, prover->challenges);
}

void gate_sc_ml_prover_free(gate_sc_ml_prover_t* prover) {
    if (!prover) return;
    
    free(prover->challenges);
    multilinear_memo_free(prover->memo_L);
    multilinear_memo_free(prover->memo_R);
    multilinear_memo_free(prover->memo_O);
    multilinear_memo_free(prover->memo_S);
}

/* Verifier implementation */

void gate_sc_ml_verifier_init(
    gate_sc_ml_verifier_t* verifier,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum,
    size_t num_vars) {
    
    if (!verifier || !transcript) return;
    
    verifier->transcript = transcript;
    verifier->claimed_sum = claimed_sum;
    verifier->num_vars = num_vars;
    verifier->current_round = 0;
    verifier->running_claim = claimed_sum;
    
    verifier->challenges = calloc(num_vars, sizeof(gf128_t));
}

bool gate_sc_ml_verifier_round(
    gate_sc_ml_verifier_t* verifier,
    const round_polynomial_t* round_poly) {
    
    if (!verifier || !round_poly) return false;
    if (verifier->current_round >= verifier->num_vars) return false;
    
    // Add polynomial to transcript
    fs_absorb(verifier->transcript,
              round_poly->coeffs,
              sizeof(round_poly->coeffs));
    
    // Check that g(0) + g(1) = previous claim
    gf128_t g0 = round_poly->coeffs[0];
    gf128_t g1 = gf128_add(round_poly->coeffs[0], round_poly->coeffs[1]);
    // For higher degree terms at X=1
    if (round_poly->degree >= 2) {
        g1 = gf128_add(g1, round_poly->coeffs[2]);
    }
    if (round_poly->degree >= 3) {
        g1 = gf128_add(g1, round_poly->coeffs[3]);
    }
    
    gf128_t sum = gf128_add(g0, g1);
    
    if (!gf128_eq(sum, verifier->running_claim)) {
        fprintf(stderr, "SumCheck round %zu failed: g(0)+g(1) != claim\n", 
                verifier->current_round);
        fprintf(stderr, "  g(0) = %016lx%016lx\n", g0.hi, g0.lo);
        fprintf(stderr, "  g(1) = %016lx%016lx\n", g1.hi, g1.lo);
        fprintf(stderr, "  g(0)+g(1) = %016lx%016lx\n", sum.hi, sum.lo);
        fprintf(stderr, "  expected = %016lx%016lx\n", verifier->running_claim.hi, verifier->running_claim.lo);
        fprintf(stderr, "  polynomial degree = %zu\n", round_poly->degree);
        return false;
    }
    
    // Sample challenge
    uint8_t challenge_bytes[32];
    fs_challenge(verifier->transcript, challenge_bytes);
    memcpy(&verifier->challenges[verifier->current_round], challenge_bytes, sizeof(gf128_t));
    
    // Compute new claim: g(r_i)
    gf128_t r = verifier->challenges[verifier->current_round];
    gf128_t new_claim = round_poly->coeffs[0];
    gf128_t r_power = r;
    
    for (size_t i = 1; i <= round_poly->degree && i < 4; i++) {
        new_claim = gf128_add(new_claim, gf128_mul(round_poly->coeffs[i], r_power));
        if (i < round_poly->degree) {
            r_power = gf128_mul(r_power, r);
        }
    }
    
    verifier->running_claim = new_claim;
    verifier->current_round++;
    return true;
}

bool gate_sc_ml_verifier_final(
    gate_sc_ml_verifier_t* verifier,
    const gf128_t evals[4]) {
    
    if (!verifier || !evals) return false;
    
    // Compute F(z) from the evaluations
    gf128_t l_val = evals[0];
    gf128_t r_val = evals[1];
    gf128_t o_val = evals[2];
    gf128_t s_val = evals[3];
    
    // F(z) = S(z)·(L(z)·R(z)) + (1-S(z))·(L(z)+R(z)) - O(z)
    gf128_t lr_product = gf128_mul(l_val, r_val);
    gf128_t and_part = gf128_mul(s_val, lr_product);
    
    gf128_t one_minus_s = gf128_add(gf128_one(), s_val);
    gf128_t l_plus_r = gf128_add(l_val, r_val);
    gf128_t xor_part = gf128_mul(one_minus_s, l_plus_r);
    
    gf128_t f_z = gf128_add(and_part, xor_part);
    f_z = gf128_add(f_z, o_val);
    
    // Check if F(z) equals the running claim
    if (!gf128_eq(f_z, verifier->running_claim)) {
        fprintf(stderr, "SumCheck final check failed: F(z) != final claim\n");
        return false;
    }
    
    return true;
}

void gate_sc_ml_verifier_free(gate_sc_ml_verifier_t* verifier) {
    if (!verifier) return;
    free(verifier->challenges);
}

/* High-level proof generation */

gate_sumcheck_proof_t* gate_sumcheck_ml_prove(
    gate_sumcheck_instance_t* instance,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum) {
    
    if (!instance || !transcript) return NULL;
    
    gate_sumcheck_proof_t* proof = malloc(sizeof(gate_sumcheck_proof_t));
    if (!proof) return NULL;
    
    proof->num_rounds = instance->num_vars;
    proof->round_polys = malloc(proof->num_rounds * sizeof(round_polynomial_t));
    proof->final_point = malloc(proof->num_rounds * sizeof(gf128_t));
    
    if (!proof->round_polys || !proof->final_point) {
        gate_sumcheck_proof_free(proof);
        return NULL;
    }
    
    // Initialize prover
    gate_sc_ml_prover_t prover;
    gate_sc_ml_prover_init(&prover, instance, transcript);
    
    // Execute rounds
    for (size_t i = 0; i < proof->num_rounds; i++) {
        if (!gate_sc_ml_prover_round(&prover, &proof->round_polys[i])) {
            gate_sc_ml_prover_free(&prover);
            gate_sumcheck_proof_free(proof);
            return NULL;
        }
        proof->final_point[i] = prover.challenges[i];
    }
    
    // Get final evaluations
    gate_sc_ml_prover_final(&prover, proof->final_evals);
    
    gate_sc_ml_prover_free(&prover);
    return proof;
}

/* High-level verification */

bool gate_sumcheck_ml_verify(
    const gate_sumcheck_proof_t* proof,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum,
    size_t num_vars) {
    
    if (!proof || !transcript) return false;
    if (proof->num_rounds != num_vars) return false;
    
    // Initialize verifier
    gate_sc_ml_verifier_t verifier;
    gate_sc_ml_verifier_init(&verifier, transcript, claimed_sum, num_vars);
    
    // Verify rounds
    for (size_t i = 0; i < proof->num_rounds; i++) {
        if (!gate_sc_ml_verifier_round(&verifier, &proof->round_polys[i])) {
            gate_sc_ml_verifier_free(&verifier);
            return false;
        }
    }
    
    // Verify final evaluations
    bool result = gate_sc_ml_verifier_final(&verifier, proof->final_evals);
    
    gate_sc_ml_verifier_free(&verifier);
    return result;
}

/* Cleanup */

void gate_sumcheck_proof_free(gate_sumcheck_proof_t* proof) {
    if (!proof) return;
    free(proof->round_polys);
    free(proof->final_point);
    free(proof);
}