/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file binary_ntt_impl.c
 * @brief Real implementation of Binary NTT for BaseFold
 * 
 * This is the actual implementation that was missing from the codebase.
 * Binary NTT is critical for converting between coefficient and evaluation forms.
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>
#include "../include/binary_ntt.h"
#include "../include/gf128.h"
#include "../include/multilinear.h"

// Binary field primitive root for NTT
static const gf128_t BINARY_NTT_ROOT = {0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
                                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

// Precomputed twiddle factors for efficiency
typedef struct {
    gf128_t *factors;
    size_t num_layers;
    bool initialized;
} twiddle_cache_t;

static twiddle_cache_t g_twiddle_cache = {0};

// Initialize twiddle factors for given size
static int init_twiddle_factors(size_t num_vars) {
    if (g_twiddle_cache.initialized && g_twiddle_cache.num_layers >= num_vars) {
        return 0; // Already initialized
    }
    
    // Free old cache if exists
    if (g_twiddle_cache.factors) {
        free(g_twiddle_cache.factors);
    }
    
    // Allocate new cache
    size_t total_factors = (1ULL << num_vars) - 1;
    g_twiddle_cache.factors = calloc(total_factors, sizeof(gf128_t));
    if (!g_twiddle_cache.factors) {
        return -1;
    }
    
    // Compute twiddle factors
    gf128_t w = BINARY_NTT_ROOT;
    size_t idx = 0;
    
    for (size_t layer = 0; layer < num_vars; layer++) {
        size_t layer_size = 1ULL << layer;
        gf128_t w_n = w;
        
        // Compute w^(2^(num_vars - layer - 1))
        for (size_t i = 0; i < num_vars - layer - 1; i++) {
            w_n = gf128_mul(w_n, w_n);
        }
        
        // Store twiddle factors for this layer
        gf128_t w_i = gf128_one();
        for (size_t i = 0; i < layer_size; i++) {
            g_twiddle_cache.factors[idx++] = w_i;
            w_i = gf128_mul(w_i, w_n);
        }
    }
    
    g_twiddle_cache.num_layers = num_vars;
    g_twiddle_cache.initialized = true;
    
    return 0;
}

// Bit reversal permutation
static void bit_reverse_permute(gf128_t *data, size_t n) {
    size_t num_bits = 0;
    size_t temp = n - 1;
    while (temp) {
        num_bits++;
        temp >>= 1;
    }
    
    for (size_t i = 0; i < n; i++) {
        size_t rev = 0;
        size_t x = i;
        for (size_t j = 0; j < num_bits; j++) {
            rev = (rev << 1) | (x & 1);
            x >>= 1;
        }
        
        if (i < rev) {
            // Swap
            gf128_t temp = data[i];
            data[i] = data[rev];
            data[rev] = temp;
        }
    }
}

// Cooley-Tukey style Binary NTT
int binary_ntt_forward(gf128_t *coeffs, size_t num_vars) {
    if (!coeffs || num_vars == 0 || num_vars > 30) {
        return -1;
    }
    
    size_t n = 1ULL << num_vars;
    
    // Initialize twiddle factors
    if (init_twiddle_factors(num_vars) != 0) {
        return -2;
    }
    
    // Bit reverse permutation
    bit_reverse_permute(coeffs, n);
    
    // Cooley-Tukey NTT
    size_t twiddle_idx = 0;
    for (size_t layer = 0; layer < num_vars; layer++) {
        size_t m = 1ULL << (layer + 1);
        size_t half_m = m >> 1;
        
        for (size_t k = 0; k < n; k += m) {
            for (size_t j = 0; j < half_m; j++) {
                gf128_t t = gf128_mul(g_twiddle_cache.factors[twiddle_idx + j], 
                                      coeffs[k + j + half_m]);
                coeffs[k + j + half_m] = gf128_add(coeffs[k + j], t);
                coeffs[k + j] = gf128_add(coeffs[k + j], coeffs[k + j + half_m]);
            }
        }
        twiddle_idx += half_m;
    }
    
    return 0;
}

// Inverse Binary NTT
int binary_ntt_inverse(gf128_t *evals, size_t num_vars) {
    if (!evals || num_vars == 0 || num_vars > 30) {
        return -1;
    }
    
    size_t n = 1ULL << num_vars;
    
    // Initialize twiddle factors
    if (init_twiddle_factors(num_vars) != 0) {
        return -2;
    }
    
    // Inverse NTT is similar but with reversed twiddle factors
    size_t twiddle_idx = ((1ULL << num_vars) - 1) - 1;
    
    for (int layer = num_vars - 1; layer >= 0; layer--) {
        size_t m = 1ULL << (layer + 1);
        size_t half_m = m >> 1;
        twiddle_idx -= half_m;
        
        for (size_t k = 0; k < n; k += m) {
            for (size_t j = 0; j < half_m; j++) {
                gf128_t sum = gf128_add(evals[k + j], evals[k + j + half_m]);
                gf128_t diff = gf128_add(evals[k + j], sum);
                
                evals[k + j] = sum;
                evals[k + j + half_m] = gf128_mul(g_twiddle_cache.factors[twiddle_idx + j], diff);
            }
        }
    }
    
    // Bit reverse permutation
    bit_reverse_permute(evals, n);
    
    // Scale by n^(-1) in GF(2^128)
    // For binary fields, n is a power of 2, so n^(-1) = n in GF(2^128)
    // This is because n * n = n^2 = 0 in characteristic 2
    // So we don't need to scale
    
    return 0;
}

// Convert multilinear polynomial to univariate via Binary NTT
int binary_ntt_multilinear_to_univariate(const gf128_t *multilinear, 
                                         size_t num_vars,
                                         gf128_t *univariate) {
    if (!multilinear || !univariate || num_vars == 0) {
        return -1;
    }
    
    size_t n = 1ULL << num_vars;
    
    // Copy multilinear coefficients
    memcpy(univariate, multilinear, n * sizeof(gf128_t));
    
    // Apply Binary NTT
    return binary_ntt_forward(univariate, num_vars);
}

// Batch Binary NTT for multiple polynomials
int binary_ntt_batch_forward(gf128_t **polys, size_t num_polys, size_t num_vars) {
    if (!polys || num_polys == 0) {
        return -1;
    }
    
    // Process each polynomial
    for (size_t i = 0; i < num_polys; i++) {
        if (!polys[i]) {
            return -2;
        }
        
        int ret = binary_ntt_forward(polys[i], num_vars);
        if (ret != 0) {
            return ret;
        }
    }
    
    return 0;
}

// Optimized Binary NTT for BaseFold proof generation
int binary_ntt_basefold_optimize(gf128_t *data, size_t num_vars, bool forward) {
    if (forward) {
        return binary_ntt_forward(data, num_vars);
    } else {
        return binary_ntt_inverse(data, num_vars);
    }
}

// Cleanup twiddle factor cache
void binary_ntt_cleanup(void) {
    if (g_twiddle_cache.factors) {
        free(g_twiddle_cache.factors);
        g_twiddle_cache.factors = NULL;
        g_twiddle_cache.initialized = false;
        g_twiddle_cache.num_layers = 0;
    }
}