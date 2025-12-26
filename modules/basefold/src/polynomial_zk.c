#include "basefold_trace.h"
#include "polynomial_gf128.h"
#include "prg.h"
#include "secure_random_compat.h"
#include "evaluation_domain.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#ifdef __x86_64__
#include <immintrin.h>
#endif

// Forward declaration of generate_random_polynomial
static poly_gf128_t* generate_random_polynomial(size_t degree);

/**
 * @brief Convert trace data to polynomial representation
 * 
 * Converts the packed gate trace data into 4 separate polynomials
 * representing L (left inputs), R (right inputs), O (outputs), and S (selectors).
 */
static bool trace_to_polynomials(basefold_trace_t* trace) {
    if (!trace || !trace->trace_data || !trace->eval_domain) {
        return false;
    }
    
    eval_domain_t* domain = (eval_domain_t*)trace->eval_domain;
    size_t domain_size = domain->size;
    
    // Allocate polynomials for L, R, O, S
    for (int i = 0; i < 4; i++) {
        trace->witness_polys[i] = poly_new(domain_size);
        if (!trace->witness_polys[i]) {
            // Clean up on failure
            for (int j = 0; j < i; j++) {
                poly_free(trace->witness_polys[j]);
                trace->witness_polys[j] = NULL;
            }
            return false;
        }
    }
    
    // Convert trace data to field elements
    // Each gate has 4 bits: left, right, output, selector
    for (size_t i = 0; i < trace->padded_size; i++) {
        gate_trace_t gate = trace->trace_data[i];
        
        // Extract bits
        uint8_t left = gate & 1;
        uint8_t right = (gate >> 1) & 1;
        uint8_t output = (gate >> 2) & 1;
        uint8_t selector = (gate >> 3) & 1;
        
        // Convert to field elements (0 or 1)
        trace->witness_polys[0]->coeffs[i] = left ? gf128_one() : gf128_zero();
        trace->witness_polys[1]->coeffs[i] = right ? gf128_one() : gf128_zero();
        trace->witness_polys[2]->coeffs[i] = output ? gf128_one() : gf128_zero();
        trace->witness_polys[3]->coeffs[i] = selector ? gf128_one() : gf128_zero();
    }
    
    // Pad with zeros to domain size
    for (size_t i = trace->padded_size; i < domain_size; i++) {
        for (int j = 0; j < 4; j++) {
            trace->witness_polys[j]->coeffs[i] = gf128_zero();
        }
    }
    
    // Update polynomial degrees
    for (int i = 0; i < 4; i++) {
        trace->witness_polys[i]->degree = trace->padded_size > 0 ? trace->padded_size - 1 : 0;
        // Find actual degree (highest non-zero coefficient)
        while (trace->witness_polys[i]->degree > 0 && 
               gf128_is_zero(trace->witness_polys[i]->coeffs[trace->witness_polys[i]->degree])) {
            trace->witness_polys[i]->degree--;
        }
    }
    
    return true;
}

/**
 * @brief Generate random polynomial for zero-knowledge
 * 
 * Generates a random polynomial r(X) of appropriate degree using the PRG.
 */
static poly_gf128_t* generate_random_polynomial(size_t degree) {
    poly_gf128_t* r = poly_new(degree + 1);
    if (!r) return NULL;
    
    // Generate random coefficients using global PRG
    for (size_t i = 0; i <= degree; i++) {
#ifdef __x86_64__
        __m128i rand_val = prg_next();
        uint8_t rand_bytes[16];
        _mm_storeu_si128((__m128i*)rand_bytes, rand_val);
        r->coeffs[i] = gf128_from_le(rand_bytes);
#else
        uint8_t rand_bytes[16];
        prg_next(rand_bytes);
        r->coeffs[i] = gf128_from_le(rand_bytes);
#endif
    }
    
    r->degree = degree;
    return r;
}

/**
 * @brief Apply polynomial randomization for zero-knowledge
 * 
 * Implements ŵ(X) = w(X) + v_H(X) · r(X) where:
 * - w(X) is the witness polynomial
 * - v_H(X) is the vanishing polynomial of the evaluation domain
 * - r(X) is a random polynomial
 */
bool basefold_trace_apply_polynomial_zk(basefold_trace_t* trace, const uint8_t* seed) {
    if (!trace || trace->is_masked) {
        return false;
    }
    
    printf("DEBUG: Starting polynomial ZK for %u gates\n", trace->padded_size);
    
    // Initialize evaluation domain if not already done
    if (!trace->eval_domain) {
        // Domain size should be next power of 2 >= padded_size
        size_t domain_size = 1;
        while (domain_size < trace->padded_size) {
            domain_size <<= 1;
        }
        
        trace->eval_domain = domain_new(domain_size);
        if (!trace->eval_domain) {
            fprintf(stderr, "Failed to create evaluation domain\n");
            return false;
        }
    }
    
    // Convert trace to polynomial representation
    if (!trace_to_polynomials(trace)) {
        fprintf(stderr, "Failed to convert trace to polynomials\n");
        return false;
    }
    
    // Set up PRG with seed
    if (seed) {
        memcpy(trace->mask_seed, seed, 128);
    } else {
        // Generate cryptographically secure random seed
        if (!secure_random_seed_128_safe(trace->mask_seed)) {
            fprintf(stderr, "CRITICAL: Failed to generate secure random seed for ZK masking\n");
            fprintf(stderr, "Zero-knowledge security cannot be guaranteed\n");
            return false;
        }
    }
    // Compress 128-byte seed to 16 bytes for PRG
    uint8_t prg_seed[32];
    extern void sha3_hash(int type, const uint8_t *input, size_t input_len, 
                         uint8_t *output, size_t output_len);
    sha3_hash(2, trace->mask_seed, 128, prg_seed, 32); // SHA3-256
    prg_init(prg_seed); // PRG uses first 16 bytes
    
    // Compute degree for randomizer polynomial
    // Based on the security parameter and constraint degree
    size_t randomizer_degree = basefold_compute_randomizer_degree(
        2,    // constraint degree for AND/XOR gates
        128,  // number of field queries (security parameter)
        64    // number of FRI queries
    );
    
    // Generate random polynomial r(X)
    trace->randomizer_poly = generate_random_polynomial(randomizer_degree);
    if (!trace->randomizer_poly) {
        fprintf(stderr, "Failed to generate randomizer polynomial\n");
        return false;
    }
    
    // Compute vanishing polynomial v_H(X)
    poly_gf128_t* v_H = compute_vanishing_polynomial(trace->eval_domain);
    if (!v_H) {
        fprintf(stderr, "Failed to compute vanishing polynomial\n");
        return false;
    }
    
    // For each witness polynomial, compute ŵ(X) = w(X) + v_H(X) · r(X)
    for (int i = 0; i < 4; i++) {
        // Allocate masked polynomial
        trace->masked_polys[i] = poly_new(
            trace->witness_polys[i]->degree + v_H->degree + trace->randomizer_poly->degree + 1
        );
        if (!trace->masked_polys[i]) {
            poly_free(v_H);
            return false;
        }
        
        // Compute v_H(X) · r(X)
        poly_gf128_t* v_H_times_r = poly_new(v_H->degree + trace->randomizer_poly->degree + 1);
        if (!v_H_times_r || !poly_mul(v_H_times_r, v_H, trace->randomizer_poly)) {
            poly_free(v_H);
            poly_free(v_H_times_r);
            return false;
        }
        
        // Add to witness: ŵ(X) = w(X) + v_H(X) · r(X)
        if (!poly_add(trace->masked_polys[i], trace->witness_polys[i], v_H_times_r)) {
            poly_free(v_H);
            poly_free(v_H_times_r);
            return false;
        }
        
        poly_free(v_H_times_r);
    }
    
    poly_free(v_H);
    
    // Update field elements to reflect masked polynomials
    // Evaluate masked polynomials on the domain
    eval_domain_t* eval_domain = (eval_domain_t*)trace->eval_domain;
    for (size_t i = 0; i < trace->padded_size; i++) {
        gf128_t point = eval_domain->elements[i];
        
        gf128_t left_val = poly_eval(trace->masked_polys[0], point);
        gf128_t right_val = poly_eval(trace->masked_polys[1], point);
        gf128_t output_val = poly_eval(trace->masked_polys[2], point);
        gf128_t selector_val = poly_eval(trace->masked_polys[3], point);
        
        // Store in field_elements array
        size_t base_idx = i * 4;
#ifdef __x86_64__
        // Convert gf128_t to __m128i
        trace->field_elements[base_idx + 0] = _mm_set_epi64x(left_val.hi, left_val.lo);
        trace->field_elements[base_idx + 1] = _mm_set_epi64x(right_val.hi, right_val.lo);
        trace->field_elements[base_idx + 2] = _mm_set_epi64x(output_val.hi, output_val.lo);
        trace->field_elements[base_idx + 3] = _mm_set_epi64x(selector_val.hi, selector_val.lo);
#else
        // Store as bytes
        gf128_to_le(left_val, &trace->field_elements[(base_idx + 0) * 16]);
        gf128_to_le(right_val, &trace->field_elements[(base_idx + 1) * 16]);
        gf128_to_le(output_val, &trace->field_elements[(base_idx + 2) * 16]);
        gf128_to_le(selector_val, &trace->field_elements[(base_idx + 3) * 16]);
#endif
    }
    
    trace->is_masked = true;
    
    // Debug: verify that constraints still hold on evaluation domain
    if (getenv("BASEFOLD_DEBUG")) {
        eval_domain_t* debug_domain = (eval_domain_t*)trace->eval_domain;
        printf("Verifying constraints on evaluation domain...\n");
        for (size_t i = 0; i < debug_domain->size && i < trace->padded_size; i++) {
            gf128_t point = debug_domain->elements[i];
            
            gf128_t l = poly_eval(trace->witness_polys[0], point);
            gf128_t r = poly_eval(trace->witness_polys[1], point);
            gf128_t o = poly_eval(trace->witness_polys[2], point);
            gf128_t s = poly_eval(trace->witness_polys[3], point);
            
            // Check constraint: s(l·r) + (1-s)(l+r) = o
            // In GF(2^128): s·l·r + l + r + s·l + s·r = o
            gf128_t lr = gf128_mul(l, r);
            gf128_t s_lr = gf128_mul(s, lr);
            gf128_t s_l = gf128_mul(s, l);
            gf128_t s_r = gf128_mul(s, r);
            
            gf128_t constraint = gf128_add(s_lr, l);
            constraint = gf128_add(constraint, r);
            constraint = gf128_add(constraint, s_l);
            constraint = gf128_add(constraint, s_r);
            
            if (!gf128_eq(constraint, o)) {
                fprintf(stderr, "Constraint failed at position %zu\n", i);
                return false;
            }
        }
        printf("All constraints verified!\n");
    }
    
    return true;
}