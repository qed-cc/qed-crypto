#ifndef BASEFOLD_EVALUATION_DOMAIN_H
#define BASEFOLD_EVALUATION_DOMAIN_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <gf128.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Extended evaluation domain for zero-knowledge
 * 
 * Extends the boolean hypercube {0,1}^n to {0,1}^(n+2) to provide
 * a 4x larger domain for statistical zero-knowledge.
 * 
 * The extended domain is partitioned into 4 quadrants:
 * - Quadrant 0 (indices 0 to 2^n-1): Original trace values (unmasked)
 * - Quadrants 1-3: Randomized values for zero-knowledge
 */
typedef struct {
    size_t original_vars;      /**< Number of original variables (n) */
    size_t extended_vars;      /**< Number of extended variables (n+2) */
    size_t original_size;      /**< Size of original domain (2^n) */
    size_t extended_size;      /**< Size of extended domain (2^(n+2) = 4*2^n) */
    uint8_t* zk_seed;         /**< 16-byte seed for deterministic randomness */
} evaluation_domain_t;

/**
 * @brief Create an extended evaluation domain
 * 
 * @param num_original_vars Number of variables in original polynomial
 * @param zk_seed 16-byte seed for randomness generation (can be NULL for non-ZK)
 * @return New evaluation domain or NULL on error
 */
evaluation_domain_t* evaluation_domain_create(size_t num_original_vars, const uint8_t* zk_seed);

/**
 * @brief Free an evaluation domain
 * 
 * @param domain Domain to free
 */
void evaluation_domain_free(evaluation_domain_t* domain);

/**
 * @brief Map extended domain index to evaluation point
 * 
 * Converts an index in [0, 4*2^n) to a point in {0,1}^(n+2)
 * 
 * @param domain Evaluation domain
 * @param index Index in extended domain
 * @param point Output array of n+2 field elements (pre-allocated)
 */
void evaluation_domain_index_to_point(
    const evaluation_domain_t* domain,
    size_t index,
    gf128_t* point
);

/**
 * @brief Check if index is in original (unmasked) quadrant
 * 
 * @param domain Evaluation domain
 * @param index Index to check
 * @return true if index < 2^n (original quadrant)
 */
static inline bool evaluation_domain_is_original(
    const evaluation_domain_t* domain,
    size_t index
) {
    return index < domain->original_size;
}

/**
 * @brief Generate deterministic mask for extended domain point
 * 
 * For indices outside the original quadrant, generates a random
 * field element using the domain's seed.
 * 
 * @param domain Evaluation domain (must have zk_seed)
 * @param index Extended domain index
 * @param column Column index (0=L, 1=R, 2=O, 3=S)
 * @return Random mask value, or zero if in original quadrant
 */
gf128_t evaluation_domain_generate_mask(
    const evaluation_domain_t* domain,
    size_t index,
    size_t column
);

/**
 * @brief Evaluate masked polynomial on extended domain
 * 
 * For a polynomial with evaluations on {0,1}^n, computes the
 * extended evaluations on {0,1}^(n+2) with masking applied.
 * 
 * @param domain Evaluation domain
 * @param original_evals Evaluations on {0,1}^n (size 2^n)
 * @param column Column index for masking
 * @param extended_evals Output array (size 2^(n+2), pre-allocated)
 */
void evaluation_domain_extend_polynomial(
    const evaluation_domain_t* domain,
    const gf128_t* original_evals,
    size_t column,
    gf128_t* extended_evals
);

/**
 * @brief Get the quadrant of an extended domain index
 * 
 * @param domain Evaluation domain
 * @param index Extended domain index
 * @return Quadrant number (0-3)
 */
static inline size_t evaluation_domain_get_quadrant(
    const evaluation_domain_t* domain,
    size_t index
) {
    return index / domain->original_size;
}

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_EVALUATION_DOMAIN_H */