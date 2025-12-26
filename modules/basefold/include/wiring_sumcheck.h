#ifndef BASEFOLD_WIRING_SUMCHECK_H
#define BASEFOLD_WIRING_SUMCHECK_H

/**
 * @file wiring_sumcheck.h
 * @brief SumCheck protocol for wiring constraint verification in BaseFold
 * 
 * Implements the second SumCheck phase that verifies the wiring permutation
 * is correctly applied: G(u,v,x) = L(u,v,x) - L(u,v,σ(x)) + R(...) + O(...)
 * This ensures gate outputs are correctly routed to gate inputs.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "transcript.h"
#include "merkle/build.h"
#include "wiring.h"
#include "enc.h"
#include "evaluation_path.h"

/**
 * @brief Wiring SumCheck prover state
 * 
 * Maintains state across d=18 rounds of the SumCheck protocol for wiring constraints.
 * Uses the multiset equality approach from HyperPlonk Algorithm 2 to verify
 * that wiring permutation is correctly applied to all trace columns.
 */
typedef struct {
    fiat_shamir_t *transcript;       /**< Fiat-Shamir transcript for challenges */
    merkle_tree_t *tree;             /**< Merkle tree for Reed-Muller codeword */
    const gf128_t *codeword;         /**< Original 128 MiB Reed-Muller codeword */
    wiring_permutation_t *wiring;    /**< Wiring permutation σ */
    
    gf128_t challenges[D];           /**< Verifier challenges r₁,...,r_d */
    uint8_t current_round;           /**< Current round index (0 to d-1) */
    size_t codeword_size;            /**< Size of codeword in GF(128) elements */
    
    // Working space for polynomial evaluation
    gf128_t *eval_buffer;            /**< Buffer for evaluating partial sums */
    gf128_t *permuted_buffer;        /**< Buffer for σ-permuted values */
    size_t eval_size;                /**< Current evaluation buffer size */
    // Algorithm 2 buffers: precomputed wiring values and fold halves
    size_t wire_size;                /**< Number of rows (eval_size / 4 columns) */
    gf128_t *wire_vals;              /**< Initial wiring polynomial values per row */
    gf128_t *buf_even;               /**< Semi-lazy: values for even-indexed rows */
    gf128_t *buf_odd;                /**< Semi-lazy: values for odd-indexed rows */
    size_t buf_size;                 /**< Semi-lazy: number of rows in buf_even/buf_odd */
    int algo;                        /**< SumCheck algorithm: 1=default,2=semi-lazy */
    
    /* Evaluation path tracking */
    evaluation_path_t *eval_path;    /**< Tracks evaluations for binding proof */
} wiring_sc_prover_t;

/**
 * @brief Wiring SumCheck verifier state
 * 
 * Tracks verification of the wiring constraint SumCheck protocol.
 * Verifies polynomial coefficients and Merkle openings at each round.
 */
typedef struct {
    fiat_shamir_t *transcript;       /**< Fiat-Shamir transcript for challenges */
    uint8_t merkle_root[32];         /**< Merkle root from prover's commitment */
    wiring_permutation_t *wiring;    /**< Known wiring permutation σ */
    
    gf128_t challenges[D];           /**< Generated challenges r₁,...,r_d */
    gf128_t claimed_sum;             /**< Claimed sum from round 0 */
    gf128_t running_sum;             /**< Running verification sum */
    uint8_t current_round;           /**< Current round index (0 to d-1) */
} wiring_sc_verifier_t;

/**
 * @brief Initialize wiring SumCheck prover
 * 
 * @param prover Prover state structure to initialize
 * @param transcript Fiat-Shamir transcript (must be initialized)
 * @param tree Merkle tree built from Reed-Muller codeword
 * @param codeword Original Reed-Muller codeword
 * @param codeword_size Size of codeword in GF(128) elements
 * @param wiring Wiring permutation structure (must be padded)
 * 
 * Sets up the prover for wiring SumCheck protocol.
 */
void wiring_sc_init(wiring_sc_prover_t *prover, fiat_shamir_t *transcript, 
                    merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size,
                    wiring_permutation_t *wiring);

/**
 * @brief Execute one round of wiring SumCheck proving
 * 
 * @param prover Prover state
 * @param round_idx Current round index (0 to d-1)
 * @param coeffs_out Output buffer for 4 polynomial coefficients (64 bytes)
 * @return 0 on success, -1 on error
 * 
 * Computes the univariate polynomial h(X) = Σ G(r₁,...,rᵢ₋₁,X,b_{i+1},...,b_d)
 * where G is the wiring polynomial. Returns coefficients of the degree-1 polynomial.
 */
int wiring_sc_prove_round(wiring_sc_prover_t *prover, uint8_t round_idx,
                          uint8_t coeffs_out[16*4]);

/**
 * @brief Complete wiring SumCheck proving and return final scalar
 * 
 * @param prover Prover state
 * @return Final evaluation G(r₁,...,r_d) as GF(128) element
 * 
 * After d rounds, evaluates the wiring polynomial at the full challenge point.
 * For valid wiring, this should equal zero.
 */
gf128_t wiring_sc_final(wiring_sc_prover_t *prover);

/**
 * @brief Initialize wiring SumCheck verifier
 * 
 * @param verifier Verifier state structure to initialize
 * @param transcript Fiat-Shamir transcript (must match prover's)
 * @param root Merkle root from prover's commitment (32 bytes)
 * @param wiring Known wiring permutation structure
 * 
 * Prepares verifier to check d=18 rounds of wiring constraint SumCheck.
 */
void wiring_sc_verifier_init(wiring_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                             const uint8_t root[32], wiring_permutation_t *wiring);

/**
 * @brief Verify one round of wiring SumCheck
 * 
 * @param verifier Verifier state
 * @param round_idx Current round index (0 to d-1)
 * @param coeffs Polynomial coefficients from prover (64 bytes)
 * @param auth_paths Merkle authentication paths (for leaf openings)
 * @param path_lens Lengths of authentication paths in bytes
 * @return 0 if round accepts, -1 if round rejects
 * 
 * Verifies polynomial consistency and Merkle openings for wiring constraints.
 */
int wiring_sc_verifier_round(wiring_sc_verifier_t *verifier, uint8_t round_idx,
                             const uint8_t coeffs[16*4],
                             const uint8_t *auth_paths[], size_t path_lens[]);

/**
 * @brief Complete wiring SumCheck verification
 * 
 * @param verifier Verifier state
 * @param final_scalar Final evaluation from prover
 * @return 0 if proof accepts, -1 if proof rejects
 * 
 * Verifies that the final scalar equals zero (for valid wiring constraints).
 */
int wiring_sc_verifier_final(wiring_sc_verifier_t *verifier, gf128_t final_scalar);

/**
 * @brief Free wiring SumCheck prover resources
 * 
 * @param prover Prover state to clean up
 */
void wiring_sc_prover_free(wiring_sc_prover_t *prover);

/**
 * @brief Generate evaluation path proof for binding verification
 * 
 * @param prover Prover state (after completing all rounds)
 * @param challenge_point The challenge point from sumcheck
 * @return Evaluation path proof structure (caller must free)
 * 
 * This function generates a proof that binds the Merkle openings
 * to the sumcheck evaluation path, preventing the prover from
 * opening different polynomials during the protocol.
 */
evaluation_path_proof_t* wiring_sc_get_eval_path_proof(wiring_sc_prover_t *prover,
                                                      const gf128_t *challenge_point);

/**
 * @brief Evaluate wiring polynomial G(u,v,x) for given inputs
 * 
 * @param trace_vals Values from trace at position x: [L(x), R(x), O(x), S(x)]
 * @param permuted_vals Values from trace at σ(x): [L(σ(x)), R(σ(x)), O(σ(x)), S(σ(x))]
 * @return G(...) = L(x) - L(σ(x)) + R(x) - R(σ(x)) + O(x) - O(σ(x))
 * 
 * Helper function for testing and verification.
 * Returns zero if and only if the wiring is correctly applied.
 */
gf128_t wiring_polynomial_eval(const gf128_t trace_vals[4], const gf128_t permuted_vals[4]);

#endif /* BASEFOLD_WIRING_SUMCHECK_H */