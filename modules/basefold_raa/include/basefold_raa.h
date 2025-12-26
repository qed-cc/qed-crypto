/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef BASEFOLD_RAA_H
#define BASEFOLD_RAA_H

#include <stdint.h>
#include <stddef.h>
#include "../../gf128/include/gf128.h"

/**
 * @file basefold_raa.h
 * @brief BaseFold RAA hybrid proof system API
 * 
 * Combines BaseFold's sumcheck protocol with RAA (Randomized Affine Aggregation)
 * encoding to achieve:
 * - ~150ms proof generation for SHA3-256 (192,086 gates)
 * - ~190KB proof size with 320 queries
 * - 122-bit effective soundness (post-quantum secure)
 */

#ifdef __cplusplus
extern "C" {
#endif

/* Configuration constants */
#define BASEFOLD_RAA_SECURITY_BITS 122  /* Effective soundness limited by sumcheck */
#define BASEFOLD_RAA_REPETITION_FACTOR 4
#define BASEFOLD_RAA_NUM_QUERIES 320  /* Required for 122-bit security */

/**
 * @brief RAA encoding parameters
 */
typedef struct {
    size_t message_len;      /* Original message length (k) */
    size_t codeword_len;     /* Encoded length (n = r*k) */
    size_t repetition;       /* Repetition factor (r) */
    size_t* perm1;          /* First permutation */
    size_t* perm2;          /* Second permutation */
    uint8_t seed[32];       /* Seed for deterministic generation */
} basefold_raa_params_t;

/**
 * @brief BaseFold RAA proof structure
 */
typedef struct {
    /* Sumcheck phase */
    uint8_t* sumcheck_commitments;  /* Commitments for each round */
    gf128_t* sumcheck_responses;    /* Polynomial evaluations per round */
    size_t num_sumcheck_rounds;     /* Number of variables */
    
    /* RAA commitment phase */
    uint8_t raa_root[32];           /* Merkle root of RAA codeword */
    size_t raa_codeword_size;       /* Size of encoded polynomial */
    
    /* Opening phase */
    gf128_t claimed_eval;           /* Claimed polynomial evaluation */
    gf128_t* query_values;          /* RAA codeword at query positions */
    gf128_t** query_leaf_values;    /* Complete leaf values (8 per leaf) for Merkle verification */
    uint8_t** merkle_paths;         /* Authentication paths */
    size_t* query_indices;          /* Query positions */
    size_t num_queries;             /* Number of queries */
    
    /* Zero-knowledge */
    gf128_t* randomizer_coeffs;     /* Randomizer polynomial coefficients */
    size_t randomizer_degree;       /* Degree of randomizer polynomial */
    uint8_t mask_seed[32];          /* Seed used for polynomial masking */
    
    /* Metadata */
    size_t witness_size;            /* Original witness size */
    uint8_t proof_tag[32];          /* Fiat-Shamir binding */
} basefold_raa_proof_t;

/**
 * @brief Configuration for proof generation
 */
typedef struct {
    size_t num_variables;           /* Number of variables (log of witness size) */
    size_t security_level;          /* Target security in bits */
    int enable_zk;                  /* Enable zero-knowledge */
    int num_threads;                /* OpenMP thread count (0 = auto) */
} basefold_raa_config_t;

/* Main API functions */

/**
 * @brief Initialize RAA parameters
 * @param params Output parameter structure
 * @param message_len Length of message to encode
 * @param repetition Repetition factor (typically 4)
 * @param seed 32-byte seed for deterministic permutation generation
 * @return 0 on success, negative on error
 */
int basefold_raa_init_params(basefold_raa_params_t* params,
                            size_t message_len,
                            size_t repetition,
                            const uint8_t seed[32]);

/**
 * @brief Free RAA parameters
 * @param params Parameters to free
 */
void basefold_raa_free_params(basefold_raa_params_t* params);

/**
 * @brief Generate proof for multilinear polynomial
 * @param witness Evaluations over boolean hypercube (size 2^num_vars)
 * @param config Proof configuration
 * @param proof Output proof structure
 * @return 0 on success, negative on error
 */
int basefold_raa_prove(const gf128_t* witness,
                      const basefold_raa_config_t* config,
                      basefold_raa_proof_t* proof);

/**
 * @brief Verify proof
 * @param proof Proof to verify
 * @param config Configuration used for proof generation
 * @return 0 if valid, negative if invalid
 */
int basefold_raa_verify(const basefold_raa_proof_t* proof,
                       const basefold_raa_config_t* config);

/**
 * @brief Free proof structure
 * @param proof Proof to free
 */
void basefold_raa_proof_free(basefold_raa_proof_t* proof);

/**
 * @brief Get estimated proof size
 * @param config Configuration
 * @return Estimated proof size in bytes
 */
size_t basefold_raa_proof_size(const basefold_raa_config_t* config);

/* Utility functions */

/**
 * @brief RAA encode a message
 * @param message Input message
 * @param params RAA parameters
 * @param codeword Output codeword (must be pre-allocated)
 * @return 0 on success, negative on error
 */
int basefold_raa_encode(const gf128_t* message,
                       const basefold_raa_params_t* params,
                       gf128_t* codeword);

/**
 * @brief Verify RAA codeword consistency
 * @param codeword Codeword to check
 * @param params RAA parameters
 * @param indices Query indices
 * @param num_queries Number of queries
 * @return 0 if consistent, negative if not
 */
int basefold_raa_verify_consistency(const gf128_t* codeword,
                                   const basefold_raa_params_t* params,
                                   const size_t* indices,
                                   size_t num_queries);

/* Additional types for RAS integration */

/* Forward declarations */
typedef struct basefold_raa_prover basefold_raa_prover_t;
typedef struct basefold_raa_verifier basefold_raa_verifier_t;

/* Use the proof type directly */
typedef basefold_raa_proof_t basefold_proof_t;

/* Field type enumeration */
typedef enum {
    FIELD_GF128 = 0,
    FIELD_GF256 = 1
} basefold_field_type_t;

/* Configuration management */
basefold_raa_config_t* basefold_raa_config_init(void);
void basefold_raa_config_free(basefold_raa_config_t* config);
void basefold_raa_config_set_field(basefold_raa_config_t* config, basefold_field_type_t field);
void basefold_raa_config_set_security_level(basefold_raa_config_t* config, size_t bits);
void basefold_raa_config_enable_zk(basefold_raa_config_t* config, int enable);

/* Prover/Verifier management */
basefold_raa_prover_t* basefold_raa_prover_init(const basefold_raa_config_t* config);
void basefold_raa_prover_free(basefold_raa_prover_t* prover);
basefold_raa_verifier_t* basefold_raa_verifier_init(const basefold_raa_config_t* config);
void basefold_raa_verifier_free(basefold_raa_verifier_t* verifier);

/* Proof operations for RAS */
basefold_proof_t* basefold_proof_placeholder_create(const basefold_raa_config_t* config);
basefold_proof_t* basefold_proof_copy(const basefold_proof_t* proof);
basefold_proof_t* basefold_proof_recursive_compose(basefold_raa_prover_t* prover,
                                                   const basefold_proof_t* proof1,
                                                   const basefold_proof_t* proof2);
void basefold_proof_free(basefold_proof_t* proof);
size_t basefold_proof_size(const basefold_proof_t* proof);
int basefold_proof_verify(basefold_raa_verifier_t* verifier, const basefold_proof_t* proof);
int basefold_proof_serialize(const basefold_proof_t* proof, uint8_t* buffer, size_t buffer_len);
basefold_proof_t* basefold_proof_deserialize(const uint8_t* buffer, size_t buffer_len);

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_RAA_H */