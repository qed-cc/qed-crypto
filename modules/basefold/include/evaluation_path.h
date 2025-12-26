#ifndef BASEFOLD_EVALUATION_PATH_H
#define BASEFOLD_EVALUATION_PATH_H

/**
 * @file evaluation_path.h
 * @brief Evaluation path tracking for Merkle-sumcheck binding
 * 
 * SECURITY CRITICAL: This ensures the Merkle commitment properly
 * binds to the sumcheck polynomial evaluation.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "gf128.h"
#include "merkle/build.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Merkle node structure
 */
typedef struct {
    uint8_t hash[32];  /**< SHA3-256 hash of the node */
} merkle_node_t;

/**
 * @brief Merkle proof for a single opening
 */
typedef struct {
    uint8_t hash[32];     /**< Hash of the opened leaf */
    uint32_t index;       /**< Index in the tree */
} merkle_proof_t;

/**
 * @brief Evaluation path for multilinear polynomial
 * 
 * Tracks the evaluations at each round of sumcheck
 */
typedef struct {
    uint32_t num_vars;            /**< Number of variables (depth of path) */
    gf128_t* evaluations;         /**< Evaluations at each round */
    merkle_node_t* merkle_nodes;  /**< Merkle nodes for each round */
} evaluation_path_t;

/**
 * @brief Evaluation path proof structure
 * 
 * Contains the proof that binds Merkle openings to sumcheck
 */
typedef struct {
    uint32_t num_vars;              /**< Number of variables */
    gf128_t* path_evaluations;      /**< Evaluations along the path */
    merkle_proof_t* merkle_proofs;  /**< Merkle proofs for each evaluation */
    gf128_t final_evaluation;       /**< Final evaluation value */
} evaluation_path_proof_t;

/**
 * @brief Initialize evaluation path structure
 * 
 * @param num_vars Number of variables in the multilinear polynomial
 * @return Allocated path structure, or NULL on error
 */
evaluation_path_t* evaluation_path_init(uint32_t num_vars);

/**
 * @brief Free evaluation path structure
 * 
 * @param path Path to free
 */
void evaluation_path_free(evaluation_path_t* path);

/**
 * @brief Record evaluation at a specific round
 * 
 * @param path Evaluation path structure
 * @param round Round number (0-indexed)
 * @param evaluation The evaluation value for this round
 * @param node Optional Merkle node for this round
 */
void evaluation_path_record(evaluation_path_t* path, uint32_t round, 
                          gf128_t evaluation, const merkle_node_t* node);

/**
 * @brief Generate evaluation path proof
 * 
 * @param path The evaluation path with recorded values
 * @param challenge_point The challenge point from sumcheck
 * @param tree The Merkle tree
 * @return Evaluation path proof structure (caller must free)
 */
evaluation_path_proof_t* evaluation_path_prove(const evaluation_path_t* path,
                                              const gf128_t* challenge_point,
                                              const merkle_tree_t* tree);

/**
 * @brief Verify evaluation path proof
 * 
 * @param proof The evaluation path proof
 * @param challenge_point The challenge point from sumcheck
 * @param merkle_root The Merkle root to verify against
 * @param expected_final The expected final evaluation
 * @return true if valid, false if invalid
 */
bool evaluation_path_verify(const evaluation_path_proof_t* proof,
                          const gf128_t* challenge_point,
                          const uint8_t* merkle_root,
                          gf128_t expected_final);

/**
 * @brief Free evaluation path proof
 * 
 * @param proof Proof structure to free
 */
void evaluation_path_proof_free(evaluation_path_proof_t* proof);

/**
 * @brief Interpolate between two values
 * 
 * Computes (1-r)·val0 + r·val1 in GF(2^128)
 * 
 * @param val0 Value at 0
 * @param val1 Value at 1
 * @param r Interpolation point
 * @return Interpolated value
 */
static inline gf128_t interpolate_gf128(gf128_t val0, gf128_t val1, gf128_t r) {
    gf128_t one_minus_r = gf128_add(gf128_one(), r);  // In GF(2^128), 1-r = 1+r
    gf128_t term0 = gf128_mul(one_minus_r, val0);
    gf128_t term1 = gf128_mul(r, val1);
    return gf128_add(term0, term1);
}

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_EVALUATION_PATH_H */