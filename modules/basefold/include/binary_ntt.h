/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef BINARY_NTT_H
#define BINARY_NTT_H

#include <stdint.h>
#include <stddef.h>
#include "gf128.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file binary_ntt.h
 * @brief Binary Number Theoretic Transform for GF(2^128)
 * 
 * Implements the Binary NTT (also known as Additive NTT) for converting
 * between multilinear and univariate polynomial representations over GF(2^128).
 * 
 * This is a critical component of BaseFold+RAA for efficient polynomial
 * commitment and evaluation.
 */

/**
 * @brief Binary NTT context structure
 * 
 * Contains precomputed values for efficient transform computation
 */
typedef struct {
    size_t num_variables;      /* log2 of polynomial size */
    size_t size;              /* 2^num_variables */
    gf128_t* basis;           /* Multiplicative basis elements */
    gf128_t* basis_inv;       /* Inverse basis elements */
    void* scratch;            /* Scratch space for computation */
} binary_ntt_ctx_t;

/**
 * @brief Initialize Binary NTT context
 * 
 * @param ctx Context to initialize
 * @param num_variables Number of variables (log2 of size)
 * @return 0 on success, negative on error
 */
int binary_ntt_init(binary_ntt_ctx_t* ctx, size_t num_variables);

/**
 * @brief Free Binary NTT context
 * 
 * @param ctx Context to free
 */
void binary_ntt_free(binary_ntt_ctx_t* ctx);

/**
 * @brief Forward Binary NTT transform
 * 
 * Converts multilinear polynomial evaluations over the boolean hypercube
 * to univariate polynomial coefficients.
 * 
 * @param ctx Initialized context
 * @param multilinear_evals Input evaluations (size 2^num_variables)
 * @param univariate_coeffs Output coefficients (size 2^num_variables)
 * @return 0 on success, negative on error
 */
int binary_ntt_forward(const binary_ntt_ctx_t* ctx,
                      const gf128_t* multilinear_evals,
                      gf128_t* univariate_coeffs);

/**
 * @brief Inverse Binary NTT transform
 * 
 * Converts univariate polynomial coefficients back to multilinear
 * polynomial evaluations over the boolean hypercube.
 * 
 * @param ctx Initialized context
 * @param univariate_coeffs Input coefficients (size 2^num_variables)
 * @param multilinear_evals Output evaluations (size 2^num_variables)
 * @return 0 on success, negative on error
 */
int binary_ntt_inverse(const binary_ntt_ctx_t* ctx,
                      const gf128_t* univariate_coeffs,
                      gf128_t* multilinear_evals);

/**
 * @brief In-place forward Binary NTT
 * 
 * Performs the transform in-place to save memory.
 * 
 * @param ctx Initialized context
 * @param data Input/output array (size 2^num_variables)
 * @return 0 on success, negative on error
 */
int binary_ntt_forward_inplace(const binary_ntt_ctx_t* ctx, gf128_t* data);

/**
 * @brief In-place inverse Binary NTT
 * 
 * Performs the inverse transform in-place to save memory.
 * 
 * @param ctx Initialized context
 * @param data Input/output array (size 2^num_variables)
 * @return 0 on success, negative on error
 */
int binary_ntt_inverse_inplace(const binary_ntt_ctx_t* ctx, gf128_t* data);

/**
 * @brief Generate basis elements for Binary NTT
 * 
 * Generates the multiplicative basis used for the transform.
 * For GF(2^128), we need a basis of 128 linearly independent elements.
 * 
 * @param basis Output array (size num_variables)
 * @param num_variables Number of basis elements to generate
 * @return 0 on success, negative on error
 */
int binary_ntt_generate_basis(gf128_t* basis, size_t num_variables);

/**
 * @brief Butterfly operation for Binary NTT
 * 
 * Core operation of the transform.
 * 
 * @param a First element (modified in place)
 * @param b Second element (modified in place)
 * @param w Twiddle factor
 */
static inline void binary_ntt_butterfly(gf128_t* a, gf128_t* b, gf128_t w) {
    gf128_t t = gf128_mul(*b, w);
    *b = gf128_add(*a, t);
    *a = gf128_add(*a, *b);
}

#ifdef __cplusplus
}
#endif

#endif /* BINARY_NTT_H */