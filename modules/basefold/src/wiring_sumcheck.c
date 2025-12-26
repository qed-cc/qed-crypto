/**
 * @file wiring_sumcheck.c
 * @brief SumCheck protocol implementation for wiring constraints
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "wiring_sumcheck.h"
#include "gf128.h"
#include "enc.h"

gf128_t wiring_polynomial_eval(const gf128_t trace_vals[4], const gf128_t permuted_vals[4]) {
    // G(x) = L(x) - L(σ(x)) + R(x) - R(σ(x)) + O(x) - O(σ(x))
    // Note: We skip S(x) since selector bits don't need wiring constraints
    
    gf128_t result = gf128_zero();
    
    // Add L(x) - L(σ(x))
    result = gf128_add(result, gf128_add(trace_vals[0], permuted_vals[0]));
    
    // Add R(x) - R(σ(x))  
    result = gf128_add(result, gf128_add(trace_vals[1], permuted_vals[1]));
    
    // Add O(x) - O(σ(x))
    result = gf128_add(result, gf128_add(trace_vals[2], permuted_vals[2]));
    
    return result;
}

void wiring_sc_init(wiring_sc_prover_t *prover, fiat_shamir_t *transcript, 
                    merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size,
                    wiring_permutation_t *wiring) {
    assert(prover != NULL);
    assert(transcript != NULL);
    assert(tree != NULL);
    assert(codeword != NULL);
    assert(codeword_size > 0);
    assert(wiring != NULL);
    
    prover->transcript = transcript;
    prover->tree = tree;
    prover->codeword = codeword;
    prover->wiring = wiring;
    prover->current_round = 0;
    prover->eval_path = evaluation_path_init(D);  // Initialize evaluation path
    
    // Use provided codeword and wiring to initialize for SumCheck protocol
    prover->codeword_size = codeword_size;
    prover->algo = 2;  // Use algorithm 2 (semi-lazy) for best performance in wiring
    memset(prover->challenges, 0, sizeof(prover->challenges));
    prover->wire_vals = NULL;

    size_t num_rows = codeword_size / 4;
    prover->wire_size = num_rows;
    prover->eval_buffer = NULL;
    prover->permuted_buffer = NULL;
    prover->buf_even = NULL;
    prover->buf_odd = NULL;
    prover->buf_size = 0;

    if (prover->algo == 2) {
        // Semi-lazy: precompute wiring values and split into even/odd buffers
        size_t half = num_rows / 2;
        
        // SECURITY FIX: Check for integer overflow before allocation
        if (half > SIZE_MAX / sizeof(gf128_t)) {
            fprintf(stderr, "Error: Integer overflow in wiring buffer allocation\n");
            return;
        }
        
        gf128_t *e = malloc(half * sizeof(gf128_t));
        gf128_t *o = malloc(half * sizeof(gf128_t));
        if (!e || !o) {
            free(e); free(o);
            return;
        }
        for (size_t i = 0; i < half; i++) {
            size_t idx0 = 2 * i;
            size_t idx1 = idx0 + 1;
            gf128_t trace0[4], trace1[4], perm0[4], perm1[4];
            for (int col = 0; col < 4; col++) {
                trace0[col] = codeword[idx0 * 4 + col];
                trace1[col] = codeword[idx1 * 4 + col];
            }
            uint32_t s0 = wiring_get_destination(wiring, (uint32_t)idx0);
            uint32_t s1 = wiring_get_destination(wiring, (uint32_t)idx1);
            for (int col = 0; col < 4; col++) {
                perm0[col] = (s0 != UINT32_MAX && s0 < num_rows)
                             ? codeword[s0 * 4 + col]
                             : trace0[col];
                perm1[col] = (s1 != UINT32_MAX && s1 < num_rows)
                             ? codeword[s1 * 4 + col]
                             : trace1[col];
            }
            e[i] = wiring_polynomial_eval(trace0, perm0);
            o[i] = wiring_polynomial_eval(trace1, perm1);
        }
        prover->buf_even = e;
        prover->buf_odd  = o;
        prover->buf_size = half;
    } else {
        // Default: allocate buffers for incremental polynomial evaluation
        prover->eval_size = codeword_size;
        
        // SECURITY FIX: Check for integer overflow before allocation
        if (codeword_size > SIZE_MAX / sizeof(gf128_t)) {
            fprintf(stderr, "Error: Integer overflow in eval buffer allocation\n");
            prover->eval_size = 0;
            return;
        }
        
        prover->eval_buffer = malloc(codeword_size * sizeof(gf128_t));
        prover->permuted_buffer = malloc(codeword_size * sizeof(gf128_t));
        if (!prover->eval_buffer || !prover->permuted_buffer) {
            free(prover->eval_buffer);
            free(prover->permuted_buffer);
            prover->eval_buffer = prover->permuted_buffer = NULL;
            prover->eval_size = 0;
            return;
        }
        memcpy(prover->eval_buffer, codeword, codeword_size * sizeof(gf128_t));
        for (size_t i = 0; i < num_rows; i++) {
            uint32_t s = wiring_get_destination(wiring, (uint32_t)i);
            for (int col = 0; col < 4; col++) {
                prover->permuted_buffer[i * 4 + col] =
                    (s != UINT32_MAX && s < num_rows)
                    ? codeword[s * 4 + col]
                    : codeword[i * 4 + col];
            }
        }
    }
}

static void compute_wiring_round_polynomial(wiring_sc_prover_t *prover, uint8_t round_idx,
                                          gf128_t coeffs[4]) {
    // Compute univariate polynomial h(X) for current round
    // h(X) = Σ_{remaining variables} G(r₁,...,r_{i-1},X,b_{i+1},...,b_d)
    
    size_t current_size = prover->eval_size >> 1; // Half size for next round
    
    // SECURITY FIX: Check for integer overflow before allocation
    if (current_size > SIZE_MAX / sizeof(gf128_t)) {
        fprintf(stderr, "Error: Integer overflow in wiring buffer allocation\n");
        memset(coeffs, 0, 4 * sizeof(gf128_t));
        return;
    }
    
    gf128_t *next_buffer = malloc(current_size * sizeof(gf128_t));
    gf128_t *next_permuted = malloc(current_size * sizeof(gf128_t));
    
    if (!next_buffer || !next_permuted) {
        free(next_buffer);
        free(next_permuted);
        memset(coeffs, 0, 4 * sizeof(gf128_t));
        return;
    }
    
    // Initialize polynomial coefficients to zero
    coeffs[0] = gf128_zero(); // h(0)
    coeffs[1] = gf128_zero(); // h(1)
    coeffs[2] = gf128_zero(); // unused (degree 1 polynomial)
    coeffs[3] = gf128_zero(); // unused
    
    // Evaluate polynomial at X=0 and X=1 by summing over remaining variables
    for (size_t i = 0; i < current_size / 4; i++) {
        size_t left_idx = 2 * i;
        size_t right_idx = 2 * i + 1;
        
        // SECURITY FIX: Check for integer overflow in index calculations
        if (left_idx > SIZE_MAX / 4 || right_idx > SIZE_MAX / 4) {
            fprintf(stderr, "Error: Integer overflow in index calculation\n");
            memset(coeffs, 0, 4 * sizeof(gf128_t));
            free(next_buffer);
            free(next_permuted);
            return;
        }
        
        // Bounds check for buffer access
        if ((left_idx * 4 + 3) >= prover->eval_size || (right_idx * 4 + 3) >= prover->eval_size) {
            memset(coeffs, 0, 4 * sizeof(gf128_t));
            free(next_buffer);
            free(next_permuted);
            return;
        }
        
        // Extract trace values for both assignments of current variable
        gf128_t left_trace[4], right_trace[4];
        gf128_t left_permuted[4], right_permuted[4];
        
        for (int col = 0; col < 4; col++) {
            left_trace[col] = prover->eval_buffer[(left_idx * 4) + col];
            right_trace[col] = prover->eval_buffer[(right_idx * 4) + col];
            left_permuted[col] = prover->permuted_buffer[(left_idx * 4) + col];
            right_permuted[col] = prover->permuted_buffer[(right_idx * 4) + col];
        }
        
        // Evaluate wiring polynomial for X=0 (left assignment)
        gf128_t g_left = wiring_polynomial_eval(left_trace, left_permuted);
        coeffs[0] = gf128_add(coeffs[0], g_left);
        
        // Evaluate wiring polynomial for X=1 (right assignment)  
        gf128_t g_right = wiring_polynomial_eval(right_trace, right_permuted);
        coeffs[1] = gf128_add(coeffs[1], g_right);
        
        // Prepare next round's buffers using challenge from previous round
        if (round_idx > 0) {
            gf128_t challenge = prover->challenges[round_idx - 1];
            gf128_t one_minus_r = gf128_add(gf128_one(), challenge);
            gf128_mul_ctx_t ctx_c, ctx_om;
            gf128_mul_ctx_init(&ctx_c, challenge);
            gf128_mul_ctx_init(&ctx_om, one_minus_r);
            /* Linear combination: (1-r)·left + r·right for each column */
            for (int col = 0; col < 4; col++) {
                gf128_t left_val = prover->eval_buffer[(left_idx * 4) + col];
                gf128_t right_val = prover->eval_buffer[(right_idx * 4) + col];
                gf128_t interpolated = gf128_add(
                    gf128_mul_ctx_mul(&ctx_om, left_val),
                    gf128_mul_ctx_mul(&ctx_c, right_val)
                );
                next_buffer[i * 4 + col] = interpolated;
                /* Same for permuted values */
                gf128_t left_perm = prover->permuted_buffer[(left_idx * 4) + col];
                gf128_t right_perm = prover->permuted_buffer[(right_idx * 4) + col];
                gf128_t perm_interpolated = gf128_add(
                    gf128_mul_ctx_mul(&ctx_om, left_perm),
                    gf128_mul_ctx_mul(&ctx_c, right_perm)
                );
                next_permuted[i * 4 + col] = perm_interpolated;
            }
        } else {
            // First round: copy data directly (no interpolation yet)
            for (int col = 0; col < 4; col++) {
                next_buffer[i * 4 + col] = prover->eval_buffer[(left_idx * 4) + col];
                next_permuted[i * 4 + col] = prover->permuted_buffer[(left_idx * 4) + col];
            }
        }
    }
    
    // Update evaluation buffers for next round
    free(prover->eval_buffer);
    free(prover->permuted_buffer);
    prover->eval_buffer = next_buffer;
    prover->permuted_buffer = next_permuted;
    prover->eval_size = current_size;
}

int wiring_sc_prove_round(wiring_sc_prover_t *prover, uint8_t round_idx,
                          uint8_t coeffs_out[16*4]) {
    if (!prover || !coeffs_out || round_idx >= D) {
        return -1;
    }
    // Algorithm 2: semi-lazy SumCheck over precomputed wire_vals
    if (prover->algo == 2 && prover->buf_even && prover->buf_odd) {
        size_t n = prover->buf_size;
        // Compute h(0) and h(1)
        gf128_t h0 = gf128_zero(), h1 = gf128_zero();
        for (size_t i = 0; i < n; i++) {
            h0 = gf128_add(h0, prover->buf_even[i]);
            h1 = gf128_add(h1, prover->buf_odd[i]);
        }
        // Output coefficients: h(0), h(1)
        memcpy(coeffs_out + 0*16, &h0, 16);
        memcpy(coeffs_out + 1*16, &h1, 16);
        memset(coeffs_out + 2*16, 0, 16);
        memset(coeffs_out + 3*16, 0, 16);
        // Fiat-Shamir absorption and challenge
        fs_absorb(prover->transcript, coeffs_out, 64);
        uint8_t cb[32]; fs_challenge(prover->transcript, cb);
        gf128_t r = gf128_from_bytes(cb);
        prover->challenges[round_idx] = r;
        
        // Record evaluation for this round if tracking evaluation path
        if (prover->eval_path) {
            // Compute h(r) = h(0) + r * (h(1) - h(0))
            gf128_t diff = gf128_add(h1, h0);
            gf128_t eval = gf128_add(h0, gf128_mul(r, diff));
            evaluation_path_record(prover->eval_path, round_idx, eval, NULL);
        }
        // Fold even/odd buffers for next round
        gf128_t om = gf128_add(gf128_one(), r);
        gf128_mul_ctx_t ctx_r, ctx_om;
        gf128_mul_ctx_init(&ctx_r, r);
        gf128_mul_ctx_init(&ctx_om, om);
        size_t m = n / 2;
        gf128_t *e2 = malloc(m * sizeof(gf128_t));
        gf128_t *o2 = malloc(m * sizeof(gf128_t));
        if (!e2 || !o2) return -1;
        for (size_t i = 0; i < m; i++) {
            e2[i] = gf128_add(
                gf128_mul_ctx_mul(&ctx_om, prover->buf_even[2*i]),
                gf128_mul_ctx_mul(&ctx_r,    prover->buf_even[2*i+1])
            );
            o2[i] = gf128_add(
                gf128_mul_ctx_mul(&ctx_om, prover->buf_odd[2*i]),
                gf128_mul_ctx_mul(&ctx_r,    prover->buf_odd[2*i+1])
            );
        }
        free(prover->buf_even);
        free(prover->buf_odd);
        prover->buf_even = e2;
        prover->buf_odd  = o2;
        prover->buf_size = m;
        prover->current_round = round_idx + 1;
        return 0;
    }
    
    gf128_t coeffs[4];
    compute_wiring_round_polynomial(prover, round_idx, coeffs);
    
    // Copy coefficients to output buffer (16 bytes per GF(128) element)
    memcpy(coeffs_out + 0*16, &coeffs[0], 16);
    memcpy(coeffs_out + 1*16, &coeffs[1], 16);
    memcpy(coeffs_out + 2*16, &coeffs[2], 16);
    memcpy(coeffs_out + 3*16, &coeffs[3], 16);
    
    // Send coefficients to transcript for Fiat-Shamir
    fs_absorb(prover->transcript, coeffs_out, 64);
    
    // Sample challenge for this round
    uint8_t challenge_bytes[32];
    fs_challenge(prover->transcript, challenge_bytes);
    gf128_t challenge = gf128_from_bytes(challenge_bytes);
    prover->challenges[round_idx] = challenge;
    prover->current_round = round_idx + 1;
    
    // Record evaluation for this round if tracking evaluation path
    if (prover->eval_path) {
        // Compute h(challenge) = h(0) + challenge * (h(1) - h(0))
        gf128_t h0, h1;
        memcpy(&h0, coeffs_out + 0 * 16, 16);
        memcpy(&h1, coeffs_out + 1 * 16, 16);
        gf128_t diff = gf128_add(h1, h0);
        gf128_t eval = gf128_add(h0, gf128_mul(challenge, diff));
        evaluation_path_record(prover->eval_path, round_idx, eval, NULL);
    }
    
    return 0;
}

gf128_t wiring_sc_final(wiring_sc_prover_t *prover) {
    if (!prover || prover->current_round != D) {
        return gf128_zero();
    }
    
    // Algorithm 2 final scalar: combine even/odd buffers
    if (prover->algo == 2 && prover->buf_even && prover->buf_odd) {
        if (prover->buf_size != 1) return gf128_zero();
        gf128_t h0 = prover->buf_even[0];
        gf128_t h1 = prover->buf_odd[0];
        gf128_t diff = gf128_add(h1, h0);
        gf128_t r = prover->challenges[prover->current_round - 1];
        return gf128_add(h0, gf128_mul(r, diff));
    }
    // Default: sum of differences
    if (prover->eval_size != 4) return gf128_zero();
    gf128_t final_trace[4], final_permuted[4];
    for (int col = 0; col < 4; col++) {
        final_trace[col] = prover->eval_buffer[col];
        final_permuted[col] = prover->permuted_buffer[col];
    }
    return wiring_polynomial_eval(final_trace, final_permuted);
}

void wiring_sc_prover_free(wiring_sc_prover_t *prover) {
    if (prover) {
        free(prover->eval_buffer);
        free(prover->permuted_buffer);
        free(prover->wire_vals);
        free(prover->buf_even);
        free(prover->buf_odd);
        prover->eval_buffer = NULL;
        prover->permuted_buffer = NULL;
        prover->wire_vals = NULL;
        prover->buf_even = NULL;
        prover->buf_odd = NULL;
        prover->eval_size = 0;
        prover->wire_size = 0;
        prover->buf_size = 0;
        
        // Free evaluation path if it exists
        if (prover->eval_path) {
            evaluation_path_free(prover->eval_path);
            prover->eval_path = NULL;
        }
    }
}

evaluation_path_proof_t* wiring_sc_get_eval_path_proof(wiring_sc_prover_t *prover,
                                                      const gf128_t *challenge_point) {
    if (!prover || !prover->eval_path || !challenge_point) {
        return NULL;
    }
    
    // Generate the evaluation path proof
    return evaluation_path_prove(prover->eval_path, challenge_point, prover->tree);
}

void wiring_sc_verifier_init(wiring_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                             const uint8_t root[32], wiring_permutation_t *wiring) {
    assert(verifier != NULL);
    assert(transcript != NULL);
    assert(root != NULL);
    assert(wiring != NULL);
    
    verifier->transcript = transcript;
    memcpy(verifier->merkle_root, root, 32);
    verifier->wiring = wiring;
    verifier->current_round = 0;
    verifier->claimed_sum = gf128_zero();
    verifier->running_sum = gf128_zero();
    
    // Initialize challenges array
    memset(verifier->challenges, 0, sizeof(verifier->challenges));
}

int wiring_sc_verifier_round(wiring_sc_verifier_t *verifier, uint8_t round_idx,
                             const uint8_t coeffs[16*4],
                             const uint8_t *auth_paths[], size_t path_lens[]) {
    if (!verifier || !coeffs || round_idx >= D) {
        return -1;
    }
    
    // Extract polynomial coefficients
    gf128_t h_coeffs[4];
    memcpy(&h_coeffs[0], coeffs + 0*16, 16);
    memcpy(&h_coeffs[1], coeffs + 1*16, 16);
    memcpy(&h_coeffs[2], coeffs + 2*16, 16);
    memcpy(&h_coeffs[3], coeffs + 3*16, 16);
    
    // SECURITY: Validate polynomial degree
    // The wiring polynomial G(x) = L(x) - L(σ(x)) + R(x) - R(σ(x)) + O(x) - O(σ(x))
    // is a linear combination of trace values, so it has degree 1 in each variable.
    // In each sumcheck round, the univariate polynomial h(X) should have degree at most 1.
    // Therefore h_coeffs[2] and h_coeffs[3] must be zero for honest provers.
    if (!gf128_is_zero(h_coeffs[2]) || !gf128_is_zero(h_coeffs[3])) {
        // Polynomial has degree > 1, which indicates a malicious prover
        return -1; // Reject: polynomial degree too high
    }
    
    // Check consistency: h(0) + h(1) should equal claimed sum from previous round
    gf128_t sum_check = gf128_add(h_coeffs[0], h_coeffs[1]);
    if (round_idx == 0) {
        // First round: store claimed sum
        verifier->claimed_sum = sum_check;
        verifier->running_sum = sum_check;
    } else {
        // Later rounds: verify consistency
        if (!gf128_eq(sum_check, verifier->running_sum)) {
            return -1; // Inconsistent polynomial
        }
    }
    
    // Update transcript and sample challenge
    fs_absorb(verifier->transcript, coeffs, 64);
    uint8_t challenge_bytes[32];
    fs_challenge(verifier->transcript, challenge_bytes);
    gf128_t challenge = gf128_from_bytes(challenge_bytes);
    verifier->challenges[round_idx] = challenge;
    
    // Compute h(challenge) for next round
    verifier->running_sum = gf128_add(h_coeffs[0], 
                                     gf128_mul(challenge, h_coeffs[1]));
    
    verifier->current_round = round_idx + 1;
    return 0;
}

int wiring_sc_verifier_final(wiring_sc_verifier_t *verifier, gf128_t final_scalar) {
    if (!verifier || verifier->current_round != D) {
        return -1;
    }
    
    // Check that final scalar matches expected evaluation
    if (!gf128_eq(final_scalar, verifier->running_sum)) {
        return -1;
    }
    
    // For valid wiring constraints, the sum should be zero
    if (!gf128_eq(verifier->claimed_sum, gf128_zero())) {
        return -1;
    }
    
    return 0;
}