#ifndef BASEFOLD_MERKLE_COMMITMENT_H
#define BASEFOLD_MERKLE_COMMITMENT_H

/**
 * @file merkle_commitment.h
 * @brief Merkle tree commitment openings for zero-knowledge proofs
 * 
 * Provides functionality to create and verify Merkle opening proofs
 * for polynomial evaluations in the BaseFold protocol.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "merkle/build.h"
#include "merkle/verify.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Merkle opening proof for a single evaluation point
 * 
 * Contains the authentication path from leaf to root
 */
typedef struct {
    uint32_t leaf_index;        /**< Index of the leaf in the tree */
    gf128_t leaf_values[8];     /**< The 8 GF128 values in this leaf */
    uint8_t* auth_path;         /**< Authentication path (sibling hashes) */
    size_t path_len;            /**< Length of authentication path */
} merkle_opening_t;

/**
 * @brief Collection of Merkle openings for sumcheck verification
 */
typedef struct {
    merkle_opening_t** openings;    /**< Array of opening proofs */
    size_t num_openings;            /**< Number of openings */
    uint8_t root[32];               /**< Merkle root for verification */
} merkle_commitment_proof_t;

/**
 * @brief Create Merkle opening proof for a specific leaf with codeword
 * 
 * @param tree Merkle tree containing the committed values
 * @param codeword The original codeword data
 * @param codeword_size Size of the codeword
 * @param leaf_index Index of the leaf to open
 * @param opening Output opening proof
 * @return 0 on success, -1 on error
 */
int merkle_create_opening_with_codeword(
    const merkle_tree_t* tree,
    const gf128_t* codeword,
    size_t codeword_size,
    uint32_t leaf_index,
    merkle_opening_t* opening);

/**
 * @brief Create Merkle opening proof for a specific leaf (DEPRECATED)
 * 
 * @deprecated Use merkle_create_opening_with_codeword instead
 * @param tree Merkle tree containing the committed values
 * @param leaf_index Index of the leaf to open
 * @param opening Output opening proof
 * @return 0 on success, -1 on error
 */
int merkle_create_opening(
    const merkle_tree_t* tree,
    uint32_t leaf_index,
    merkle_opening_t* opening
);

/**
 * @brief Create opening proofs for sumcheck final evaluation
 * 
 * After sumcheck reduces to a single point, we need to open the
 * commitments at that point to verify the final evaluation.
 * 
 * @param tree Merkle tree with committed polynomials
 * @param eval_point The evaluation point from sumcheck
 * @param num_vars Number of variables (log2 of domain size)
 * @param proof Output commitment proof
 * @return 0 on success, -1 on error
 */
int merkle_create_sumcheck_openings(
    const merkle_tree_t* tree,
    const gf128_t* eval_point,
    size_t num_vars,
    merkle_commitment_proof_t* proof
);

/**
 * @brief Verify Merkle opening proof
 * 
 * @param opening Opening proof to verify
 * @param root Expected Merkle root
 * @return true if opening is valid
 */
bool merkle_verify_opening(
    const merkle_opening_t* opening,
    const uint8_t root[32]
);

/**
 * @brief Verify all openings in a commitment proof
 * 
 * @param proof Commitment proof containing multiple openings
 * @return true if all openings are valid
 */
bool merkle_verify_commitment_proof(
    const merkle_commitment_proof_t* proof
);

/**
 * @brief Serialize commitment proof for transmission
 * 
 * @param proof Proof to serialize
 * @param buffer Output buffer
 * @param buffer_size Size of output buffer
 * @return Number of bytes written, or -1 on error
 */
int merkle_serialize_commitment_proof(
    const merkle_commitment_proof_t* proof,
    uint8_t* buffer,
    size_t buffer_size
);

/**
 * @brief Deserialize commitment proof from buffer
 * 
 * @param buffer Input buffer
 * @param buffer_size Size of input buffer
 * @param proof Output proof structure
 * @return Number of bytes read, or -1 on error
 */
int merkle_deserialize_commitment_proof(
    const uint8_t* buffer,
    size_t buffer_size,
    merkle_commitment_proof_t* proof
);

/**
 * @brief Free commitment proof resources
 * 
 * @param proof Proof to free
 */
void merkle_commitment_proof_free(merkle_commitment_proof_t* proof);

/**
 * @brief Compute leaf index from evaluation point
 * 
 * Maps an evaluation point in {0,1}^n to a leaf index in the Merkle tree
 * 
 * @param eval_point Binary evaluation point
 * @param num_vars Number of variables
 * @return Leaf index
 */
uint32_t merkle_point_to_leaf_index(
    const gf128_t* eval_point,
    size_t num_vars
);

/**
 * @brief Generate Merkle proof for sumcheck final evaluation
 * 
 * Note: This function is defined in sumcheck_merkle_proof.c and requires
 * gate_sumcheck_multilinear.h to be included before this header.
 * 
 * @param sumcheck_instance The sumcheck instance with evaluation point (gate_sumcheck_ml_t*)
 * @param tree The Merkle tree containing committed values
 * @param proof Output proof structure
 * @return 0 on success, -1 on error
 */
int generate_sumcheck_merkle_proof(
    const void* sumcheck_instance,  // Actually const gate_sumcheck_ml_t*
    const merkle_tree_t* tree,
    merkle_commitment_proof_t* proof
);

/**
 * @brief Free memory allocated for commitment proof
 * 
 * @param proof Proof structure to free
 */
void merkle_free_commitment_proof(merkle_commitment_proof_t* proof);

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_MERKLE_COMMITMENT_H */