/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "binary_ntt.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/**
 * @brief Initialize Binary NTT context
 * 
 * The Binary NTT over GF(2^128) uses a carefully chosen multiplicative basis
 * to enable efficient polynomial conversion.
 */
int binary_ntt_init(binary_ntt_ctx_t* ctx, size_t num_variables) {
    if (!ctx || num_variables == 0 || num_variables > 128) {
        return -1;
    }
    
    ctx->num_variables = num_variables;
    ctx->size = 1ULL << num_variables;
    
    // Allocate basis elements
    ctx->basis = aligned_alloc(64, num_variables * sizeof(gf128_t));
    if (!ctx->basis) {
        return -2;
    }
    
    ctx->basis_inv = aligned_alloc(64, num_variables * sizeof(gf128_t));
    if (!ctx->basis_inv) {
        free(ctx->basis);
        return -2;
    }
    
    // Allocate scratch space for in-place operations
    ctx->scratch = aligned_alloc(64, ctx->size * sizeof(gf128_t));
    if (!ctx->scratch) {
        free(ctx->basis);
        free(ctx->basis_inv);
        return -2;
    }
    
    // Generate the multiplicative basis
    if (binary_ntt_generate_basis(ctx->basis, num_variables) != 0) {
        binary_ntt_free(ctx);
        return -3;
    }
    
    // Compute inverse basis elements
    for (size_t i = 0; i < num_variables; i++) {
        ctx->basis_inv[i] = gf128_inv(ctx->basis[i]);
    }
    
    return 0;
}

/**
 * @brief Free Binary NTT context
 */
void binary_ntt_free(binary_ntt_ctx_t* ctx) {
    if (!ctx) return;
    
    if (ctx->basis) {
        free(ctx->basis);
        ctx->basis = NULL;
    }
    
    if (ctx->basis_inv) {
        free(ctx->basis_inv);
        ctx->basis_inv = NULL;
    }
    
    if (ctx->scratch) {
        free(ctx->scratch);
        ctx->scratch = NULL;
    }
    
    ctx->num_variables = 0;
    ctx->size = 0;
}

/**
 * @brief Generate basis elements for Binary NTT
 * 
 * For GF(2^128), we need linearly independent elements that form a
 * multiplicative basis. We use powers of a primitive element.
 */
int binary_ntt_generate_basis(gf128_t* basis, size_t num_variables) {
    if (!basis || num_variables == 0 || num_variables > 128) {
        return -1;
    }
    
    // Start with a primitive element of GF(2^128)
    // The element x (represented as 2) is primitive in our field
    gf128_t primitive = gf128_from_bytes((uint8_t[]){2, 0, 0, 0, 0, 0, 0, 0, 
                                                     0, 0, 0, 0, 0, 0, 0, 0});
    
    // Generate basis as powers of the primitive element
    // This ensures linear independence
    gf128_t current = gf128_one();
    for (size_t i = 0; i < num_variables; i++) {
        basis[i] = current;
        current = gf128_mul(current, primitive);
    }
    
    return 0;
}

/**
 * @brief Core butterfly operation for forward transform
 */
static void forward_butterfly_layer(gf128_t* data, size_t size, 
                                   size_t stride, gf128_t basis_elem) {
    size_t half_stride = stride / 2;
    
    for (size_t i = 0; i < size; i += stride) {
        for (size_t j = 0; j < half_stride; j++) {
            size_t idx1 = i + j;
            size_t idx2 = i + j + half_stride;
            
            // Butterfly: (a, b) -> (a + b, a + b*w)
            gf128_t a = data[idx1];
            gf128_t b = data[idx2];
            
            data[idx1] = gf128_add(a, b);
            data[idx2] = gf128_add(a, gf128_mul(b, basis_elem));
        }
    }
}

/**
 * @brief Core butterfly operation for inverse transform
 */
static void inverse_butterfly_layer(gf128_t* data, size_t size, 
                                   size_t stride, gf128_t basis_inv_elem) {
    size_t half_stride = stride / 2;
    
    for (size_t i = 0; i < size; i += stride) {
        for (size_t j = 0; j < half_stride; j++) {
            size_t idx1 = i + j;
            size_t idx2 = i + j + half_stride;
            
            // Inverse butterfly: (a, b) -> ((a + b)/2, (a - b)/(2w))
            gf128_t a = data[idx1];
            gf128_t b = data[idx2];
            
            gf128_t sum = gf128_add(a, b);
            gf128_t diff = gf128_sub(a, b);
            
            data[idx1] = sum;  // Division by 2 in GF(2^n) is just the value
            data[idx2] = gf128_mul(diff, basis_inv_elem);
        }
    }
}

/**
 * @brief Forward Binary NTT transform
 * 
 * Converts multilinear evaluations to univariate coefficients
 */
int binary_ntt_forward(const binary_ntt_ctx_t* ctx,
                      const gf128_t* multilinear_evals,
                      gf128_t* univariate_coeffs) {
    if (!ctx || !multilinear_evals || !univariate_coeffs) {
        return -1;
    }
    
    // Copy input to output
    memcpy(univariate_coeffs, multilinear_evals, ctx->size * sizeof(gf128_t));
    
    // Perform in-place transform
    return binary_ntt_forward_inplace(ctx, univariate_coeffs);
}

/**
 * @brief In-place forward Binary NTT
 */
int binary_ntt_forward_inplace(const binary_ntt_ctx_t* ctx, gf128_t* data) {
    if (!ctx || !data) {
        return -1;
    }
    
    // Apply butterfly layers
    size_t stride = 2;
    for (size_t layer = 0; layer < ctx->num_variables; layer++) {
        forward_butterfly_layer(data, ctx->size, stride, ctx->basis[layer]);
        stride *= 2;
    }
    
    return 0;
}

/**
 * @brief Inverse Binary NTT transform
 * 
 * Converts univariate coefficients back to multilinear evaluations
 */
int binary_ntt_inverse(const binary_ntt_ctx_t* ctx,
                      const gf128_t* univariate_coeffs,
                      gf128_t* multilinear_evals) {
    if (!ctx || !univariate_coeffs || !multilinear_evals) {
        return -1;
    }
    
    // Copy input to output
    memcpy(multilinear_evals, univariate_coeffs, ctx->size * sizeof(gf128_t));
    
    // Perform in-place transform
    return binary_ntt_inverse_inplace(ctx, multilinear_evals);
}

/**
 * @brief In-place inverse Binary NTT
 */
int binary_ntt_inverse_inplace(const binary_ntt_ctx_t* ctx, gf128_t* data) {
    if (!ctx || !data) {
        return -1;
    }
    
    // Apply inverse butterfly layers (reverse order)
    size_t stride = ctx->size;
    for (int layer = ctx->num_variables - 1; layer >= 0; layer--) {
        inverse_butterfly_layer(data, ctx->size, stride, ctx->basis_inv[layer]);
        stride /= 2;
    }
    
    return 0;
}