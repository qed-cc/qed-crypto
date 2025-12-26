#ifndef BASEFOLD_GATE_SUMCHECK_H
#define BASEFOLD_GATE_SUMCHECK_H

/**
 * @file gate_sumcheck.h
 * @brief SumCheck protocol for gate constraint verification in BaseFold
 * 
 * Implements the first SumCheck phase that verifies every gate satisfies its
 * boolean constraint: F(u,v,x) = s·(L·R - O) + (1-s)·(L + R - O) = 0
 * where s=0 for XOR gates, s=1 for AND gates.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "transcript.h"
#include "merkle/build.h"
#include "enc.h"
#include "evaluation_path.h"

/**
 * @brief Gate SumCheck prover state
 * 
 * Maintains state across d=18 rounds of the SumCheck protocol for gate constraints.
 * Each round the prover sends 4 GF(128) coefficients representing the univariate
 * polynomial g(X) = F(r₁,...,rᵢ₋₁,X,uᵢ₊₁,...,u_d) where F is the gate polynomial.
 */
typedef struct {
    fiat_shamir_t *transcript;      /**< Fiat-Shamir transcript for challenges */
    merkle_tree_t *tree;            /**< Merkle tree for Reed-Muller codeword */
    const gf128_t *codeword;        /**< Original 128 MiB Reed-Muller codeword */
    
    gf128_t challenges[D];          /**< Verifier challenges r₁,...,r_d */
    uint8_t current_round;          /**< Current round index (0 to d-1) */
    size_t codeword_size;           /**< Size of codeword in GF(128) elements */
    
    // Working space for polynomial evaluation
    gf128_t *eval_buffer;           /**< Buffer for evaluating partial sums (algo1/3) */
    size_t eval_size;               /**< Current evaluation buffer size */
    int algo;                       /**< SumCheck algorithm: 1,2,3 */
    /* Algorithm 2 buffers */
    gf128_t *buf_even;              /**< Algorithm2: f(0, rest) values */
    gf128_t *buf_odd;               /**< Algorithm2: f(1, rest) values */
    size_t buf_size;                /**< Algorithm2: current size of even/odd buffers */
    
    /* Zero-knowledge support */
    uint8_t has_zk;                 /**< Flag indicating if ZK is enabled */
    uint8_t zk_seed[32];            /**< ZK seed for deterministic masking */
    
    /* Evaluation path tracking */
    evaluation_path_t *eval_path;    /**< Tracks evaluations for binding proof */
} gate_sc_prover_t;

/**
 * @brief Gate SumCheck verifier state
 * 
 * Tracks verification of the gate constraint SumCheck protocol.
 * Verifies polynomial coefficients and Merkle openings at each round.
 */
typedef struct {
    fiat_shamir_t *transcript;      /**< Fiat-Shamir transcript for challenges */
    uint8_t merkle_root[32];        /**< Merkle root from prover's commitment */
    
    gf128_t challenges[D];          /**< Generated challenges r₁,...,r_d */
    gf128_t claimed_sum;            /**< Claimed sum from round 0 */
    gf128_t running_sum;            /**< Running verification sum */
    uint8_t current_round;          /**< Current round index (0 to d-1) */
    
    /* Zero-knowledge support */
    uint8_t has_zk;                 /**< Flag indicating if ZK is enabled */
    uint8_t zk_seed[32];            /**< ZK seed for deterministic masking */
} gate_sc_verifier_t;

/**
 * @brief Initialize gate SumCheck prover
 * 
 * @param prover Prover state structure to initialize
 * @param transcript Fiat-Shamir transcript (must be initialized)
 * @param tree Merkle tree built from Reed-Muller codeword
 * @param codeword Original Reed-Muller codeword
 * @param codeword_size Size of codeword in GF(128) elements
 * 
 * Sets up the prover for SumCheck protocol.
 * The codeword must contain the masked trace m'(u,v,x) with 4 columns:
 * - Column 0: Left input bits (L)
 * - Column 1: Right input bits (R) 
 * - Column 2: Output bits (O)
 * - Column 3: Selector bits (S) - 0=XOR, 1=AND
 */
void gate_sc_init(gate_sc_prover_t *prover, fiat_shamir_t *transcript, 
                  merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size);

/**
 * @brief Initialize gate SumCheck prover with zero-knowledge support
 * 
 * @param prover Prover state structure to initialize
 * @param transcript Fiat-Shamir transcript (must be initialized)
 * @param tree Merkle tree built from Reed-Muller codeword
 * @param codeword Original Reed-Muller codeword
 * @param codeword_size Size of codeword in GF(128) elements
 * @param has_zk Flag indicating if ZK is enabled
 * @param zk_seed ZK seed for deterministic masking (16 bytes, padded to 32)
 * 
 * Sets up the prover for SumCheck protocol with optional ZK masking.
 */
void gate_sc_init_zk(gate_sc_prover_t *prover, fiat_shamir_t *transcript, 
                     merkle_tree_t *tree, const gf128_t *codeword, size_t codeword_size,
                     uint8_t has_zk, const uint8_t zk_seed[16]);

/**
 * @brief Execute one round of gate SumCheck proving
 * 
 * @param prover Prover state
 * @param round_idx Current round index (0 to d-1)
 * @param coeffs_out Output buffer for 4 polynomial coefficients (64 bytes)
 * @return 0 on success, -1 on error
 * 
 * Computes the univariate polynomial g(X) = Σ F(r₁,...,rᵢ₋₁,X,b_{i+1},...,b_d)
 * over all boolean assignments to remaining variables. Returns coefficients of
 * the degree-1 polynomial as 4 GF(128) elements.
 * 
 * After sending coeffs_out, the verifier samples challenge rᵢ and both parties
 * proceed to round i+1.
 */
int gate_sc_prove_round(gate_sc_prover_t *prover, uint8_t round_idx,
                        uint8_t coeffs_out[16*4]);

/**
 * @brief Complete gate SumCheck proving and return final scalar
 * 
 * @param prover Prover state
 * @return Final evaluation F(r₁,...,r_d) as GF(128) element
 * 
 * After d rounds, evaluates the gate polynomial at the full challenge point.
 * This requires opening 4 specific leaves in the Merkle tree corresponding
 * to the challenge point (r₁,...,r_d).
 */
gf128_t gate_sc_final(gate_sc_prover_t *prover);

/**
 * @brief Initialize gate SumCheck verifier
 * 
 * @param verifier Verifier state structure to initialize
 * @param transcript Fiat-Shamir transcript (must match prover's)
 * @param root Merkle root from prover's commitment (32 bytes)
 * 
 * Prepares verifier to check d=18 rounds of gate constraint SumCheck.
 */
void gate_sc_verifier_init(gate_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                           const uint8_t root[32]);

/**
 * @brief Initialize gate SumCheck verifier with zero-knowledge support
 * 
 * @param verifier Verifier state structure to initialize
 * @param transcript Fiat-Shamir transcript (must match prover's)
 * @param root Merkle root from prover's commitment (32 bytes)
 * @param has_zk Flag indicating if ZK is enabled (from proof header)
 * @param zk_seed ZK seed for deterministic masking (16 bytes, padded to 32)
 * 
 * Prepares verifier to check d=18 rounds with optional ZK masking.
 */
void gate_sc_verifier_init_zk(gate_sc_verifier_t *verifier, fiat_shamir_t *transcript,
                              const uint8_t root[32], uint8_t has_zk, const uint8_t zk_seed[16]);

/**
 * @brief Verify one round of gate SumCheck
 * 
 * @param verifier Verifier state
 * @param round_idx Current round index (0 to d-1)
 * @param coeffs Polynomial coefficients from prover (64 bytes)
 * @param auth_paths Merkle authentication paths (for leaf openings)
 * @param path_lens Lengths of authentication paths in bytes
 * @return 0 if round accepts, -1 if round rejects
 * 
 * Verifies that:
 * 1. g(0) + g(1) equals the previous round's evaluation
 * 2. All Merkle openings are valid against the committed root
 * 3. Samples fresh challenge rᵢ for next round
 */
int gate_sc_verifier_round(gate_sc_verifier_t *verifier, uint8_t round_idx,
                           const uint8_t coeffs[16*4],
                           const uint8_t *auth_paths[], size_t path_lens[]);

/**
 * @brief Complete gate SumCheck verification
 * 
 * @param verifier Verifier state
 * @param final_scalar Final evaluation from prover
 * @return 0 if proof accepts, -1 if proof rejects
 * 
 * Verifies that the final scalar equals the expected gate polynomial evaluation
 * at the challenge point. For valid gates, this should be zero.
 */
int gate_sc_verifier_final(gate_sc_verifier_t *verifier, gf128_t final_scalar);

/**
 * @brief Free gate SumCheck prover resources
 * 
 * @param prover Prover state to clean up
 */
void gate_sc_prover_free(gate_sc_prover_t *prover);

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
evaluation_path_proof_t* gate_sc_get_eval_path_proof(gate_sc_prover_t *prover,
                                                    const gf128_t *challenge_point);

/**
 * @brief Evaluate gate polynomial F(u,v,x) for given inputs
 * 
 * @param left_input Left input bit (L)
 * @param right_input Right input bit (R)
 * @param output Output bit (O)
 * @param selector Selector bit (S) - 0=XOR, 1=AND
 * @return F(L,R,O,S) = S·(L·R - O) + (1-S)·(L + R - O)
 * 
 * Helper function for testing and verification.
 * Returns zero if and only if the gate satisfies its constraint.
 */
gf128_t gate_polynomial_eval(gf128_t left_input, gf128_t right_input, 
                            gf128_t output, gf128_t selector);

/**
 * @brief ZERO-COPY Row-Major Gate SumCheck initialization
 * 
 * @param prover Prover state structure to initialize
 * @param transcript Fiat-Shamir transcript (must be initialized)
 * @param tree Merkle tree built from Reed-Muller codeword
 * @param gates_row_major Original gate data in row-major layout [L0,R0,O0,S0][L1,R1,O1,S1]...
 * @param num_gates Number of gates (not field elements)
 * @param has_zk Flag indicating if ZK is enabled
 * @param zk_seed ZK seed for deterministic masking (16 bytes)
 * 
 * This revolutionary function eliminates the transpose bottleneck by working
 * directly on the row-major gate layout, saving 0.1+ seconds!
 */
void gate_sc_init_row_major(gate_sc_prover_t *prover, fiat_shamir_t *transcript,
                             merkle_tree_t *tree, const gf128_t *gates_row_major,
                             size_t num_gates, uint8_t has_zk, const uint8_t *zk_seed);

/**
 * @brief Execute one round of row-major gate sumcheck
 * 
 * @param prover Prover state (must be initialized with gate_sc_init_row_major)
 * @param round_idx Current round index (0 to d-1)
 * @param coeffs_out Output buffer for 4 polynomial coefficients (64 bytes)
 * @return 0 on success, -1 on error
 * 
 * Computes round polynomial directly from row-major data without transpose.
 */
int gate_sc_prove_round_row_major(gate_sc_prover_t *prover, uint8_t round_idx,
                                  uint8_t coeffs_out[16*4]);

#endif /* BASEFOLD_GATE_SUMCHECK_H */