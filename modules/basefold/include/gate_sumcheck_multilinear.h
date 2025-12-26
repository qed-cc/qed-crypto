#ifndef BASEFOLD_GATE_SUMCHECK_MULTILINEAR_H
#define BASEFOLD_GATE_SUMCHECK_MULTILINEAR_H

/**
 * @file gate_sumcheck_multilinear.h
 * @brief Multilinear polynomial version of SumCheck for gate constraints
 * 
 * Implements SumCheck protocol for multilinear polynomials as required by
 * the BaseFold paper. Verifies that the gate constraint polynomial
 * F(X) = S(X)·(L(X)·R(X)) + (1-S(X))·(L(X)+R(X)) - O(X) = 0
 * sums to zero over the boolean hypercube {0,1}^n.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "transcript.h"
#include "multilinear.h"

/**
 * @brief Gate SumCheck instance for multilinear polynomials
 */
typedef struct {
    multilinear_poly_t* L;      /**< Left input polynomial */
    multilinear_poly_t* R;      /**< Right input polynomial */
    multilinear_poly_t* O;      /**< Output polynomial */
    multilinear_poly_t* S;      /**< Selector polynomial (0=XOR, 1=AND) */
    size_t num_vars;            /**< Number of variables (log2 of gates) */
} gate_sumcheck_instance_t;

/**
 * @brief Round polynomial for SumCheck
 */
typedef struct {
    gf128_t coeffs[4];          /**< Polynomial coefficients (degree ≤ 3) */
    size_t degree;              /**< Actual degree of polynomial */
} round_polynomial_t;

/**
 * @brief SumCheck proof for gate constraints
 */
typedef struct {
    round_polynomial_t* round_polys;    /**< Round polynomials g_1, ..., g_n */
    size_t num_rounds;                  /**< Number of rounds (num_vars) */
    gf128_t* final_point;               /**< Final evaluation point */
    gf128_t final_evals[4];             /**< L(z), R(z), O(z), S(z) */
} gate_sumcheck_proof_t;

/**
 * @brief Multilinear SumCheck prover state
 */
typedef struct {
    gate_sumcheck_instance_t* instance; /**< Gate polynomials */
    fiat_shamir_t* transcript;          /**< Fiat-Shamir transcript */
    gf128_t* challenges;                /**< Accumulated challenges */
    size_t current_round;               /**< Current round index */
    
    // Working space for efficient evaluation
    multilinear_memo_t* memo_L;         /**< Memoization for L */
    multilinear_memo_t* memo_R;         /**< Memoization for R */
    multilinear_memo_t* memo_O;         /**< Memoization for O */
    multilinear_memo_t* memo_S;         /**< Memoization for S */
} gate_sc_ml_prover_t;

/**
 * @brief Fast multilinear SumCheck state (shared by prover/verifier)
 */
typedef struct {
    multilinear_poly_t* L;              /**< Left input polynomial */
    multilinear_poly_t* R;              /**< Right input polynomial */
    multilinear_poly_t* O;              /**< Output polynomial */
    multilinear_poly_t* S;              /**< Selector polynomial */
    size_t num_vars;                    /**< Number of variables */
    
    // Fast evaluation state
    gf128_t* eval_buffer;               /**< Evaluation buffer */
    size_t eval_size;                   /**< Current buffer size */
    gf128_t challenges[32];             /**< Challenges for each round */
    size_t current_round;               /**< Current round index */
    
    // Zero-knowledge support
    bool has_zk;                        /**< Whether ZK is enabled */
    uint8_t zk_seed_data[32];           /**< ZK seed storage */
    
    // Store round polynomial evaluations for proof serialization
    gf128_t round_evals[32][3];         /**< g(0), g(1), g(2) for each round */
    
    // Store reference to original codeword for Merkle proofs
    const gf128_t* original_codeword;   /**< Original codeword used to build Merkle tree */
    size_t codeword_size;               /**< Size of the codeword */
} gate_sumcheck_ml_t;

/**
 * @brief Multilinear SumCheck verifier state
 */
typedef struct {
    fiat_shamir_t* transcript;          /**< Fiat-Shamir transcript */
    gf128_t claimed_sum;                /**< Claimed sum (should be 0) */
    gf128_t* challenges;                /**< Generated challenges */
    size_t num_vars;                    /**< Number of variables */
    size_t current_round;               /**< Current round */
    gf128_t running_claim;              /**< Running claim for next round */
} gate_sc_ml_verifier_t;

/* Core functions */

/**
 * @brief Evaluate gate constraint polynomial at a point
 * 
 * Computes F(point) = S(point)·(L(point)·R(point)) + (1-S(point))·(L(point)+R(point)) - O(point)
 * 
 * @param instance Gate polynomials
 * @param point Evaluation point
 * @return F(point)
 */
gf128_t gate_constraint_ml_eval(
    const gate_sumcheck_instance_t* instance,
    const gf128_t* point
);

/**
 * @brief Generate SumCheck proof for gate constraints
 * 
 * Proves that ∑_{x∈{0,1}^n} F(x) = claimed_sum
 * 
 * @param instance Gate polynomials
 * @param transcript Fiat-Shamir transcript
 * @param claimed_sum Claimed sum (should be 0 for valid gates)
 * @return SumCheck proof
 */
gate_sumcheck_proof_t* gate_sumcheck_ml_prove(
    gate_sumcheck_instance_t* instance,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum
);

/**
 * @brief Verify SumCheck proof for gate constraints
 * 
 * @param proof SumCheck proof
 * @param transcript Fiat-Shamir transcript
 * @param claimed_sum Claimed sum
 * @param num_vars Number of variables
 * @return true if proof is valid
 */
bool gate_sumcheck_ml_verify(
    const gate_sumcheck_proof_t* proof,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum,
    size_t num_vars
);

/* Prover functions */

/**
 * @brief Initialize multilinear SumCheck prover
 * 
 * @param prover Prover state to initialize
 * @param instance Gate polynomials
 * @param transcript Fiat-Shamir transcript
 */
void gate_sc_ml_prover_init(
    gate_sc_ml_prover_t* prover,
    gate_sumcheck_instance_t* instance,
    fiat_shamir_t* transcript
);

/**
 * @brief Execute one round of proving
 * 
 * @param prover Prover state
 * @param round_poly Output round polynomial
 * @return true on success
 */
bool gate_sc_ml_prover_round(
    gate_sc_ml_prover_t* prover,
    round_polynomial_t* round_poly
);

/**
 * @brief Get final evaluations after all rounds
 * 
 * @param prover Prover state
 * @param evals Output array for L(z), R(z), O(z), S(z)
 */
void gate_sc_ml_prover_final(
    gate_sc_ml_prover_t* prover,
    gf128_t evals[4]
);

/**
 * @brief Free prover resources
 * 
 * @param prover Prover state
 */
void gate_sc_ml_prover_free(gate_sc_ml_prover_t* prover);

/* Verifier functions */

/**
 * @brief Initialize multilinear SumCheck verifier
 * 
 * @param verifier Verifier state
 * @param transcript Fiat-Shamir transcript
 * @param claimed_sum Claimed sum
 * @param num_vars Number of variables
 */
void gate_sc_ml_verifier_init(
    gate_sc_ml_verifier_t* verifier,
    fiat_shamir_t* transcript,
    gf128_t claimed_sum,
    size_t num_vars
);

/**
 * @brief Verify one round
 * 
 * @param verifier Verifier state
 * @param round_poly Round polynomial from prover
 * @return true if round accepts
 */
bool gate_sc_ml_verifier_round(
    gate_sc_ml_verifier_t* verifier,
    const round_polynomial_t* round_poly
);

/**
 * @brief Verify final evaluations
 * 
 * @param verifier Verifier state
 * @param evals Final evaluations L(z), R(z), O(z), S(z)
 * @return true if proof accepts
 */
bool gate_sc_ml_verifier_final(
    gate_sc_ml_verifier_t* verifier,
    const gf128_t evals[4]
);

/**
 * @brief Free verifier resources
 * 
 * @param verifier Verifier state
 */
void gate_sc_ml_verifier_free(gate_sc_ml_verifier_t* verifier);

/* Helper functions */

/**
 * @brief Compute round polynomial for current round
 * 
 * For round i, computes g_i(X_i) = ∑_{x_{i+1},...,x_n ∈ {0,1}} F(r_1,...,r_{i-1},X_i,x_{i+1},...,x_n)
 * 
 * @param instance Gate polynomials
 * @param round Current round (0-indexed)
 * @param challenges Previous challenges r_1, ..., r_{i-1}
 * @param round_poly Output polynomial
 */
void compute_round_polynomial_ml(
    gate_sumcheck_instance_t* instance,
    size_t round,
    const gf128_t* challenges,
    round_polynomial_t* round_poly
);

/**
 * @brief Free SumCheck proof
 * 
 * @param proof Proof to free
 */
void gate_sumcheck_proof_free(gate_sumcheck_proof_t* proof);

/* Fast O(n) multilinear sumcheck functions */

/**
 * @brief Initialize fast multilinear sumcheck prover
 * 
 * Initializes evaluation buffer with gate constraint values at all boolean points.
 * This is O(n) instead of O(2^n) because we fold the buffer each round.
 * 
 * @param instance Sumcheck instance with multilinear polynomials
 */
void gate_sumcheck_ml_fast_init(gate_sumcheck_ml_t* instance);

/**
 * @brief Initialize fast multilinear sumcheck with ZK support
 * 
 * Same as gate_sumcheck_ml_fast_init but enables polynomial randomization
 * for zero-knowledge using the provided seed.
 * 
 * @param instance Sumcheck instance with multilinear polynomials
 * @param zk_seed 32-byte seed for polynomial randomization (or NULL for no ZK)
 */
void gate_sumcheck_ml_fast_init_zk(
    gate_sumcheck_ml_t* instance,
    const uint8_t* zk_seed
);

/**
 * @brief Compute round polynomial for multilinear sumcheck - FAST O(n) version
 * 
 * Computes g(0), g(1), g(2) by summing over the current evaluation buffer.
 * 
 * @param instance Sumcheck instance
 * @param round Current round index
 * @param g_evals Output array for g(0), g(1), g(2)
 */
void compute_round_polynomial_ml_fast(
    gate_sumcheck_ml_t* instance,
    size_t round,
    gf128_t* g_evals
);

/**
 * @brief Run one round of fast multilinear sumcheck proving
 * 
 * @param instance Sumcheck instance
 * @param round Current round index
 * @param transcript Fiat-Shamir transcript
 * @param challenge_out Output challenge for this round
 * @return 0 on success, -1 on error
 */
int gate_sumcheck_ml_fast_prove_round(
    gate_sumcheck_ml_t* instance,
    size_t round,
    fiat_shamir_t* transcript,
    gf128_t* challenge_out
);

/**
 * @brief Get final evaluation after all rounds
 * 
 * @param instance Sumcheck instance
 * @return Final evaluation at the challenge point
 */
gf128_t gate_sumcheck_ml_fast_final_eval(const gate_sumcheck_ml_t* instance);

/**
 * @brief Free resources used by fast multilinear sumcheck
 * 
 * @param instance Sumcheck instance to free
 */
void gate_sumcheck_ml_fast_free(gate_sumcheck_ml_t* instance);

#endif /* BASEFOLD_GATE_SUMCHECK_MULTILINEAR_H */