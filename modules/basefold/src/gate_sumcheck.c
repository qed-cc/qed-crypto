/**
 * @file gate_sumcheck.c
 * @brief SumCheck protocol implementation for gate constraints
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include "gate_sumcheck.h"
#include "gate_sumcheck_zk.h"
#include "enc.h"
#include "gf128.h"
#include "sha3.h"


gf128_t gate_polynomial_eval(gf128_t left_input, gf128_t right_input, 
                            gf128_t output, gf128_t selector) {
    // F(L,R,O,S) = S·(L·R - O) + (1-S)·(L + R - O)
    
    // Compute L·R (using regular multiplication)
    gf128_t lr_product = gf128_mul(left_input, right_input);
    
    // Compute L·R - O  
    gf128_t lr_minus_o = gf128_add(lr_product, output);
    
    // Compute L + R
    gf128_t l_plus_r = gf128_add(left_input, right_input);
    
    // Compute L + R - O
    gf128_t lr_xor_minus_o = gf128_add(l_plus_r, output);
    
    // Compute S·(L·R - O)
    gf128_t and_term = gf128_mul(selector, lr_minus_o);
    
    // Compute (1-S) using trace format where 1 = 0x01000000...
    gf128_t trace_one;
    ((uint8_t*)&trace_one)[0] = 1;
    for (int i = 1; i < 16; i++) ((uint8_t*)&trace_one)[i] = 0;
    
    gf128_t one_minus_s = gf128_add(trace_one, selector);
    
    // Compute (1-S)·(L + R - O)
    gf128_t xor_term = gf128_mul(one_minus_s, lr_xor_minus_o);
    
    // Return S·(L·R - O) + (1-S)·(L + R - O)
    return gf128_add(and_term, xor_term);
}

void gate_sc_init(gate_sc_prover_t *prover, fiat_shamir_t *transcript, 
                  merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size) {
    assert(prover != NULL);
    assert(transcript != NULL);
    assert(tree != NULL);
    assert(codeword != NULL);
    assert(codeword_size > 0);
    
    prover->transcript = transcript;
    prover->tree = tree;
    prover->codeword = codeword;
    prover->current_round = 0;
    prover->has_zk = 0;  // No ZK by default
    memset(prover->zk_seed, 0, 32);
    prover->eval_path = NULL;  // Initialize to NULL
    
    // Use the actual codeword size provided by caller
    prover->codeword_size = codeword_size;
    
    // Select algorithm: Use algorithm 1 (standard) with constraint-preserving masking
    prover->algo = 1;  // Standard algorithm works correctly with our constraint-preserving masks
    
    // Initialize evaluation buffer for first round by computing gate constraint values
    // Codeword is arranged as 4 columns of num_rows = codeword_size/4 entries each
    // SECURITY FIX: Validate codeword size
    if (codeword_size % 4 != 0 || codeword_size == 0) {
        fprintf(stderr, "Error: Invalid codeword size %zu, must be non-zero multiple of 4\n", codeword_size);
        prover->eval_size = 0;
        return;
    }
    size_t num_rows = codeword_size / 4;
    // Check for overflow in allocation size
    if (num_rows > SIZE_MAX / sizeof(gf128_t)) {
        fprintf(stderr, "Error: Integer overflow in eval buffer allocation\n");
        prover->eval_size = 0;
        return;
    }
    prover->eval_size = num_rows;
    prover->eval_buffer = malloc(num_rows * sizeof(gf128_t));
    if (!prover->eval_buffer) {
        prover->eval_size = 0;
        return;
    }
    // Compute initial values depending on algorithm
    if (prover->algo == 3) {
        // Small-sumcheck: g'(x)=S(x)*((L⊕R⊕O)⊕(L·R⊕O))
        for (size_t i = 0; i < num_rows; i++) {
            gf128_t L = codeword[i];
            gf128_t R = codeword[num_rows + i];
            gf128_t O = codeword[2 * num_rows + i];
            gf128_t S = codeword[3 * num_rows + i];
            gf128_t a = gf128_add(gf128_add(L, R), O);
            gf128_t b = gf128_add(gf128_mul(L, R), O);
            gf128_t c = gf128_add(a, b);
            prover->eval_buffer[i] = gf128_mul(S, c);
        }
    } else {
        // Default (Algorithm 1/2): F(L,R,O,S)
        for (size_t i = 0; i < num_rows; i++) {
            gf128_t L = codeword[i];
            gf128_t R = codeword[num_rows + i];
            gf128_t O = codeword[2 * num_rows + i];
            gf128_t S = codeword[3 * num_rows + i];
            prover->eval_buffer[i] = gate_polynomial_eval(L, R, O, S);
        }
    }
    
    // Initialize challenges array
    memset(prover->challenges, 0, sizeof(prover->challenges));
    prover->buf_even = NULL;
    prover->buf_odd = NULL;
    prover->buf_size = 0;
    // If using Algorithm 2, split eval_buffer into even/odd halves
    if (prover->algo == 2) {
        size_t N = prover->eval_size;
        size_t half = N / 2;
        gf128_t *even = malloc(half * sizeof(gf128_t));
        gf128_t *odd  = malloc(half * sizeof(gf128_t));
        if (!even || !odd) {
            free(even); free(odd);
        } else {
            for (size_t i = 0; i < half; i++) {
                even[i] = prover->eval_buffer[2 * i];
                odd[i]  = prover->eval_buffer[2 * i + 1];
            }
            free(prover->eval_buffer);
            prover->eval_buffer = NULL;
            prover->buf_even = even;
            prover->buf_odd  = odd;
            prover->buf_size = half;
        }
    }
}

void gate_sc_init_zk(gate_sc_prover_t *prover, fiat_shamir_t *transcript, 
                     merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size,
                     uint8_t has_zk, const uint8_t zk_seed[16]) {
    // Initialize the base prover state
    gate_sc_init(prover, transcript, tree, codeword, codeword_size);
    
    // Set ZK parameters
    prover->has_zk = has_zk;
    if (has_zk && zk_seed) {
        // Copy the 16-byte seed and pad to 32 bytes
        memcpy(prover->zk_seed, zk_seed, 16);
        memset(prover->zk_seed + 16, 0, 16);
    }
    
    // Initialize evaluation path tracking
    prover->eval_path = evaluation_path_init(D);
}

static void compute_round_polynomial(gate_sc_prover_t *prover, uint8_t round_idx,
                                   gf128_t coeffs[2]) {
    // Compute univariate polynomial g(X) = Σ f(0, rest) and Σ f(1, rest)
    size_t num = prover->eval_size;
    size_t half = num / 2;
    coeffs[0] = gf128_zero(); // g(0)
    coeffs[1] = gf128_zero(); // g(1)
    
    for (size_t i = 0; i < half; i++) {
        gf128_t f0 = prover->eval_buffer[2 * i];
        gf128_t f1 = prover->eval_buffer[2 * i + 1];
        coeffs[0] = gf128_add(coeffs[0], f0);
        coeffs[1] = gf128_add(coeffs[1], f1);
    }
    
}
/**
 * @brief Fold evaluation buffer for next round using sampled challenge
 *
 * After sampling challenge for round i, fold the eval_buffer to prepare
 * for round i+1: new_buffer[j] = (1-r)·old_buffer[2j] + r·old_buffer[2j+1]
 */
static void fold_eval_buffer(gate_sc_prover_t *prover, uint8_t round_idx) {
    // Fold f values for next round: new_f[i] = (1-r) * f(2i) + r * f(2i+1)
    size_t num = prover->eval_size;
    size_t half = num / 2;
    gf128_t challenge = prover->challenges[round_idx];
    gf128_t one_minus = gf128_add(gf128_one(), challenge);
    gf128_t *old = prover->eval_buffer;
    gf128_t *new_buf = malloc(half * sizeof(gf128_t));
    if (!new_buf) return;
    gf128_mul_ctx_t ctx_r, ctx_om;
    gf128_mul_ctx_init(&ctx_r, challenge);
    gf128_mul_ctx_init(&ctx_om, one_minus);
    for (size_t i = 0; i < half; i++) {
        gf128_t a = old[2 * i];
        gf128_t b = old[2 * i + 1];
        gf128_t t0 = gf128_mul_ctx_mul(&ctx_om, a);
        gf128_t t1 = gf128_mul_ctx_mul(&ctx_r, b);
        new_buf[i] = gf128_add(t0, t1);
    }
    free(old);
    prover->eval_buffer = new_buf;
    prover->eval_size = half;
}

int gate_sc_prove_round(gate_sc_prover_t *prover, uint8_t round_idx,
                        uint8_t coeffs_out[16*4]) {
    if (!prover || !coeffs_out || round_idx >= D) {
        return -1;
    }
    
    // Algorithm 3: small-sumcheck for g(x)=S(x)·(A(x)⊕B(x)); uses base-field bits.
    if (prover->algo == 3) {
        size_t N = prover->eval_size;
        size_t half = N / 2;
        // Compute g(0) and g(1)
        gf128_t s0 = gf128_zero(), s1 = gf128_zero();
        for (size_t i = 0; i < half; i++) {
            s0 = gf128_add(s0, prover->eval_buffer[2*i]);
            s1 = gf128_add(s1, prover->eval_buffer[2*i+1]);
        }
        // Write coefficients
        memcpy(coeffs_out + 0*16, &s0, 16);
        memcpy(coeffs_out + 1*16, &s1, 16);
        memset(coeffs_out + 2*16, 0, 16);
        memset(coeffs_out + 3*16, 0, 16);
        
        // Apply ZK masking if enabled
        if (prover->has_zk && prover->zk_seed) {
            gf128_t mask0 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 0);
            gf128_t mask1 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 1);
            gf128_t masked0 = gf128_add(s0, mask0);
            gf128_t masked1 = gf128_add(s1, mask1);
            memcpy(coeffs_out + 0*16, &masked0, 16);
            memcpy(coeffs_out + 1*16, &masked1, 16);
        }
        
        #if 0 // Debug disabled
        if (round_idx < 3) {
            printf("Algo3 Round %d: g(0) = ", round_idx);
            gf128_print(s0);
            printf(", g(1) = ");
            gf128_print(s1);
            printf(", sum = ");
            gf128_print(gf128_add(s0, s1));
            printf(", buffer_size = %zu\n", N);
        }
        #endif
        // Transcript and challenge
        fs_absorb(prover->transcript, coeffs_out, 64);
        uint8_t cb[32]; fs_challenge(prover->transcript, cb);
        gf128_t r = gf128_from_bytes(cb);
        prover->challenges[round_idx] = r;
        
        // Record evaluation for Algorithm 3
        if (prover->eval_path) {
            gf128_t g0, g1;
            memcpy(&g0, coeffs_out + 0 * 16, 16);
            memcpy(&g1, coeffs_out + 1 * 16, 16);
            gf128_t diff = gf128_add(g1, g0);
            gf128_t eval = gf128_add(g0, gf128_mul(r, diff));
            evaluation_path_record(prover->eval_path, round_idx, eval, NULL);
        }
        // Fold buffer
        gf128_t om = gf128_add(gf128_one(), r);
        gf128_mul_ctx_t ctx_r, ctx_om;
        gf128_mul_ctx_init(&ctx_r, r);
        gf128_mul_ctx_init(&ctx_om, om);
        gf128_t *new_buf = malloc(half * sizeof(gf128_t));
        if (!new_buf) return -1;
        for (size_t i = 0; i < half; i++) {
            gf128_t a = prover->eval_buffer[2*i];
            gf128_t b = prover->eval_buffer[2*i+1];
            gf128_t t0 = gf128_mul_ctx_mul(&ctx_om, a);
            gf128_t t1 = gf128_mul_ctx_mul(&ctx_r, b);
            new_buf[i] = gf128_add(t0, t1);
        }
        free(prover->eval_buffer);
        prover->eval_buffer = new_buf;
        prover->eval_size = half;
        prover->current_round = round_idx + 1;
        return 0;
    }
    // Algorithm 2: semi-lazy SumCheck
    if (prover->algo == 2) {
        // Ensure even/odd buffers exist
        if (round_idx >= D || !prover->buf_even || !prover->buf_odd) return -1;
        // Compute g(0) and g(1)
        size_t n = prover->buf_size;
        gf128_t sum0 = gf128_zero(), sum1 = gf128_zero();
        for (size_t i = 0; i < n; i++) {
            sum0 = gf128_add(sum0, prover->buf_even[i]);
            sum1 = gf128_add(sum1, prover->buf_odd[i]);
        }
        // Write coefficients
        memcpy(coeffs_out + 0*16, &sum0, 16);
        memcpy(coeffs_out + 1*16, &sum1, 16);
        memset(coeffs_out + 2*16, 0, 16);
        memset(coeffs_out + 3*16, 0, 16);
        
        // Apply ZK masking if enabled
        if (prover->has_zk && prover->zk_seed) {
            gf128_t mask0 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 0);
            gf128_t mask1 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 1);
            gf128_t masked0 = gf128_add(sum0, mask0);
            gf128_t masked1 = gf128_add(sum1, mask1);
            memcpy(coeffs_out + 0*16, &masked0, 16);
            memcpy(coeffs_out + 1*16, &masked1, 16);
        }
        // Fiat-Shamir
        fs_absorb(prover->transcript, coeffs_out, 64);
        uint8_t cb[32]; fs_challenge(prover->transcript, cb);
        gf128_t r = gf128_from_bytes(cb);
        prover->challenges[round_idx] = r;
        
        // Record evaluation for Algorithm 2
        if (prover->eval_path) {
            gf128_t g0, g1;
            memcpy(&g0, coeffs_out + 0 * 16, 16);
            memcpy(&g1, coeffs_out + 1 * 16, 16);
            gf128_t diff = gf128_add(g1, g0);
            gf128_t eval = gf128_add(g0, gf128_mul(r, diff));
            evaluation_path_record(prover->eval_path, round_idx, eval, NULL);
        }
        // Fold buffers
        gf128_t om = gf128_add(gf128_one(), r);
        size_t m = n / 2;
        gf128_t *e2 = malloc(m * sizeof(gf128_t));
        gf128_t *o2 = malloc(m * sizeof(gf128_t));
        if (!e2 || !o2) return -1;
        for (size_t i = 0; i < m; i++) {
            e2[i] = gf128_add(gf128_mul(om, prover->buf_even[2*i]), gf128_mul(r, prover->buf_even[2*i+1]));
            o2[i] = gf128_add(gf128_mul(om, prover->buf_odd[2*i]),  gf128_mul(r, prover->buf_odd[2*i+1]));
        }
        free(prover->buf_even);
        free(prover->buf_odd);
        prover->buf_even = e2;
        prover->buf_odd  = o2;
        prover->buf_size = m;
        prover->current_round = round_idx + 1;
        return 0;
    }
    // Default (Algorithm 1)
    gf128_t coeffs[2];
    compute_round_polynomial(prover, round_idx, coeffs);
    
    // Copy coefficients to output buffer (16 bytes per GF(128) element)
    // Write g(0) and g(1) to output (coeffs 0 and 1), zero-pad unused slots
    memcpy(coeffs_out + 0 * 16, &coeffs[0], 16);
    memcpy(coeffs_out + 1 * 16, &coeffs[1], 16);
    memset(coeffs_out + 2 * 16, 0, 16);
    memset(coeffs_out + 3 * 16, 0, 16);
    
    // Apply ZK masking if enabled
    if (prover->has_zk && prover->zk_seed) {
        // Generate deterministic masks for each coefficient
        gf128_t mask0 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 0);
        gf128_t mask1 = gate_sumcheck_generate_round_mask(prover->zk_seed, round_idx, 1);
        
        // Apply masks to coefficients
        gf128_t masked0 = gf128_add(coeffs[0], mask0);
        gf128_t masked1 = gf128_add(coeffs[1], mask1);
        
        // Write masked coefficients
        memcpy(coeffs_out + 0 * 16, &masked0, 16);
        memcpy(coeffs_out + 1 * 16, &masked1, 16);
    }
    
    
    // Send coefficients to transcript for Fiat-Shamir
    fs_absorb(prover->transcript, coeffs_out, 64);
    
    // Sample challenge for this round
    uint8_t challenge_bytes[32];
    fs_challenge(prover->transcript, challenge_bytes);
    gf128_t challenge = gf128_from_bytes(challenge_bytes);
    prover->challenges[round_idx] = challenge;
    
    // Record evaluation for this round if tracking evaluation path
    if (prover->eval_path) {
        // Compute g(challenge) = g(0) + challenge * (g(1) - g(0))
        gf128_t g0, g1;
        memcpy(&g0, coeffs_out + 0 * 16, 16);
        memcpy(&g1, coeffs_out + 1 * 16, 16);
        gf128_t diff = gf128_add(g1, g0);
        gf128_t eval = gf128_add(g0, gf128_mul(challenge, diff));
        
        // Record the evaluation (no Merkle node for now)
        evaluation_path_record(prover->eval_path, round_idx, eval, NULL);
    }
    
    // Debug output removed
    // Fold evaluation buffer to prepare for next round using sampled challenge
    fold_eval_buffer(prover, round_idx);
    prover->current_round = round_idx + 1;
    
    return 0;
}

gf128_t gate_sc_final(gate_sc_prover_t *prover) {
    if (!prover || prover->current_round != D) {
        return gf128_zero();
    }
    // Algorithm 2 final fold
    if (prover->algo == 2) {
        if (prover->buf_size != 1) return gf128_zero();
        gf128_t s0 = prover->buf_even[0];
        gf128_t s1 = prover->buf_odd[0];
        gf128_t diff = gf128_add(s1, s0);
        gf128_t r = prover->challenges[prover->current_round - 1];
        return gf128_add(s0, gf128_mul(r, diff));
    }
    // Algorithm 2 final scalar
    if (prover->algo == 2) {
        if (prover->buf_size != 1) return gf128_zero();
        // The last even/odd buffers contain g_{d-1}(0) and g_{d-1}(1)
        gf128_t s0 = prover->buf_even[0];
        gf128_t s1 = prover->buf_odd[0];
        // g(r) = s0 + r * (s1 - s0)
        gf128_t diff = gf128_add(s1, s0);
        gf128_t r = prover->challenges[prover->current_round - 1];
        return gf128_add(s0, gf128_mul(r, diff));
    }
    // Default (Algorithm 1 / 3): buffer should have one element
    if (prover->eval_size != 1) {
        return gf128_zero();
    }
    return prover->eval_buffer[0];
}

void gate_sc_prover_free(gate_sc_prover_t *prover) {
    if (prover) {
        free(prover->eval_buffer);
        prover->eval_buffer = NULL;
        prover->eval_size = 0;
        
        // Free evaluation path if it exists
        if (prover->eval_path) {
            evaluation_path_free(prover->eval_path);
            prover->eval_path = NULL;
        }
    }
}

evaluation_path_proof_t* gate_sc_get_eval_path_proof(gate_sc_prover_t *prover,
                                                    const gf128_t *challenge_point) {
    if (!prover || !prover->eval_path || !challenge_point) {
        return NULL;
    }
    
    // Generate the evaluation path proof
    return evaluation_path_prove(prover->eval_path, challenge_point, prover->tree);
}

void gate_sc_verifier_init(gate_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                           const uint8_t root[32]) {
    assert(verifier != NULL);
    assert(transcript != NULL);
    assert(root != NULL);
    
    verifier->transcript = transcript;
    memcpy(verifier->merkle_root, root, 32);
    verifier->current_round = 0;
    verifier->claimed_sum = gf128_zero();
    verifier->running_sum = gf128_zero();
    
    // Initialize challenges array
    memset(verifier->challenges, 0, sizeof(verifier->challenges));
    
    // No ZK by default
    verifier->has_zk = 0;
    memset(verifier->zk_seed, 0, 32);
}

void gate_sc_verifier_init_zk(gate_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                              const uint8_t root[32], uint8_t has_zk, const uint8_t zk_seed[16]) {
    // Initialize base verifier
    gate_sc_verifier_init(verifier, transcript, root);
    
    // Set ZK parameters
    verifier->has_zk = has_zk;
    if (has_zk && zk_seed) {
        // Copy 16-byte seed and pad to 32 bytes
        memcpy(verifier->zk_seed, zk_seed, 16);
        memset(verifier->zk_seed + 16, 0, 16);
    }
}

/**
 * @brief Process one round of gate sumcheck verification
 * 
 * This function implements the verifier's role in the sumcheck protocol,
 * validating polynomial coefficients and maintaining the running sum.
 * 
 * PROTOCOL DESCRIPTION:
 * In round i, the prover sends coefficients of univariate polynomial g_i(X)
 * where g_i is the partial sum over all unfixed variables. The verifier:
 * 1. Validates polynomial degree (must be ≤ 1)
 * 2. Checks g_i(0) + g_i(1) = previous round's claim
 * 3. Samples random challenge r_i
 * 4. Computes next claim as g_i(r_i)
 * 
 * SECURITY CHECKS:
 * - Degree Validation: Rejects if deg(g_i) > 1 (prevents cheating)
 * - Consistency Check: Ensures sum preservation across rounds
 * - ZK Unmasking: Removes the same masks applied by prover
 * 
 * @param verifier Verifier state
 * @param round_idx Current round number (0 to d-1)
 * @param coeffs Polynomial coefficients (64 bytes: 4 x GF128 elements)
 * @param auth_paths Unused (for future Merkle integration)
 * @param path_lens Unused (for future Merkle integration)
 * @return 0 on success, -1 on verification failure
 */
int gate_sc_verifier_round(gate_sc_verifier_t *verifier, uint8_t round_idx,
                           const uint8_t coeffs[16*4],
                           const uint8_t *auth_paths[], size_t path_lens[]) {
    if (!verifier || !coeffs || round_idx >= D) {
        return -1;
    }
    
    // Extract polynomial coefficients
    gf128_t g_coeffs[4];
    memcpy(&g_coeffs[0], coeffs + 0*16, 16);
    memcpy(&g_coeffs[1], coeffs + 1*16, 16);
    memcpy(&g_coeffs[2], coeffs + 2*16, 16);
    memcpy(&g_coeffs[3], coeffs + 3*16, 16);
    
    // SECURITY: Validate polynomial degree
    // The gate constraint polynomial has individual degree 1 in each variable.
    // When we sum over all but one variable, the resulting univariate polynomial
    // g(X) must have degree at most 1. If the prover sends higher degree terms
    // (g_coeffs[2] or g_coeffs[3] non-zero), they are trying to cheat.
    // 
    // Mathematical justification:
    // F(L,R,O,S) = S·L·R + (1-S)·(L+R) - O
    //            = S·L·R + L + R - S·L - S·R - O
    // Each term has degree ≤ 1 in any variable, so g(X) has degree ≤ 1.
    if (!gf128_is_zero(g_coeffs[2]) || !gf128_is_zero(g_coeffs[3])) {
        return -1; // SECURITY: Reject high-degree polynomial
    }
    
    // SECURITY FIX: Apply ZK masks if enabled (must match prover's masks)
    if (verifier->has_zk) {
        // Generate same deterministic masks as prover using the same helper function
        gf128_t mask0 = gate_sumcheck_generate_round_mask(verifier->zk_seed, round_idx, 0);
        gf128_t mask1 = gate_sumcheck_generate_round_mask(verifier->zk_seed, round_idx, 1);
        
        // Subtract masks (in GF(2^128), add = subtract)
        g_coeffs[0] = gf128_add(g_coeffs[0], mask0);
        g_coeffs[1] = gf128_add(g_coeffs[1], mask1);
    }
    
    // Check consistency: g(0) + g(1) should equal claimed sum from previous round
    gf128_t sum_check = gf128_add(g_coeffs[0], g_coeffs[1]);
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
    
    // Compute g(challenge) for next round
    // Since g_coeffs[0] = g(0) and g_coeffs[1] = g(1), we need:
    // g(challenge) = g(0) + challenge * (g(1) - g(0))
    gf128_t diff = gf128_add(g_coeffs[1], g_coeffs[0]); // g(1) - g(0) in GF(2^128)
    verifier->running_sum = gf128_add(g_coeffs[0], 
                                     gf128_mul(challenge, diff));
    
    
    verifier->current_round = round_idx + 1;
    return 0;
}

int gate_sc_verifier_final(gate_sc_verifier_t *verifier, gf128_t final_scalar) {
    if (!verifier || verifier->current_round != D) {
        return -1;
    }
    
    // Check that final scalar matches expected evaluation
    if (!gf128_eq(final_scalar, verifier->running_sum)) {
        return -1;
    }
    
    // For valid gate constraints, the sum should be zero
    if (!gf128_eq(verifier->claimed_sum, gf128_zero())) {
        return -1;
    }
    
    return 0;
}