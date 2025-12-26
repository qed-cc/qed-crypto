#include "polynomial_gf128.h"
#include "input_validation.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Helper function to compute g^n using square-and-multiply */
static gf128_t gf128_pow(gf128_t base, size_t exp) {
    gf128_t result = gf128_one();
    gf128_t temp = base;
    
    while (exp > 0) {
        if (exp & 1) {
            result = gf128_mul(result, temp);
        }
        temp = gf128_mul(temp, temp);
        exp >>= 1;
    }
    
    return result;
}

/* For evaluation domains, we'll use a simple approach:
 * Instead of finding primitive roots, we'll use a coset of {1, α, α^2, ..., α^(n-1)}
 * where α is a generator of the multiplicative group */
static gf128_t get_domain_generator(size_t n) {
    // For simplicity, we'll use a fixed generator and scale it
    // In GF(2^128), we can use the element x (polynomial representation)
    uint8_t gen_bytes[16] = {0};
    gen_bytes[0] = 0x02;  // This represents the polynomial x
    return gf128_from_le(gen_bytes);
}

/* Evaluation domain operations */

eval_domain_t* domain_new(size_t size) {
    // Check that size is a power of 2
    if (size == 0 || (size & (size - 1)) != 0) {
        fprintf(stderr, "Domain size must be a power of 2\n");
        return NULL;
    }
    
    eval_domain_t* domain = malloc(sizeof(eval_domain_t));
    if (!domain) return NULL;
    
    domain->size = size;
    domain->elements = malloc(size * sizeof(gf128_t));
    domain->inv_elements = malloc(size * sizeof(gf128_t));
    
    if (!domain->elements || !domain->inv_elements) {
        free(domain->elements);
        free(domain->inv_elements);
        free(domain);
        return NULL;
    }
    
    // Use a simple generator for the domain
    domain->generator = get_domain_generator(size);
    
    // For a domain of size n, we use powers of the generator
    // This creates a multiplicative subgroup when the generator has order >= n
    domain->elements[0] = gf128_one();
    domain->inv_elements[0] = gf128_one();
    
    for (size_t i = 1; i < size; i++) {
        domain->elements[i] = gf128_mul(domain->elements[i-1], domain->generator);
        domain->inv_elements[i] = gf128_inv(domain->elements[i]);
    }
    
    return domain;
}

void domain_free(eval_domain_t* domain) {
    if (domain) {
        free(domain->elements);
        free(domain->inv_elements);
        free(domain);
    }
}

/* FFT implementation for GF(2^128) */

static void fft_recursive(gf128_t* values, size_t n, const gf128_t* roots, size_t stride) {
    if (n == 1) return;
    
    size_t half_n = n / 2;
    
    // Split into even and odd indices
    gf128_t* even = malloc(half_n * sizeof(gf128_t));
    gf128_t* odd = malloc(half_n * sizeof(gf128_t));
    
    if (!even || !odd) {
        free(even);
        free(odd);
        return;
    }
    
    for (size_t i = 0; i < half_n; i++) {
        even[i] = values[2 * i];
        odd[i] = values[2 * i + 1];
    }
    
    // Recursive FFT on even and odd parts
    fft_recursive(even, half_n, roots, stride * 2);
    fft_recursive(odd, half_n, roots, stride * 2);
    
    // Combine results
    for (size_t i = 0; i < half_n; i++) {
        gf128_t t = gf128_mul(roots[i * stride], odd[i]);
        values[i] = gf128_add(even[i], t);
        values[i + half_n] = gf128_add(even[i], t);  // In GF(2^128), add = sub
    }
    
    free(even);
    free(odd);
}

bool domain_fft(const eval_domain_t* domain, const poly_gf128_t* p, gf128_t* values) {
    if (!domain || !p || !values) return false;
    
    // Copy coefficients to values array, padding with zeros
    for (size_t i = 0; i <= p->degree && i < domain->size; i++) {
        values[i] = p->coeffs[i];
    }
    for (size_t i = p->degree + 1; i < domain->size; i++) {
        values[i] = gf128_zero();
    }
    
    // Perform FFT
    fft_recursive(values, domain->size, domain->elements, 1);
    
    return true;
}

bool domain_ifft(const eval_domain_t* domain, const gf128_t* values, poly_gf128_t* p) {
    if (!domain || !values || !p) return false;
    
    // Ensure polynomial has enough capacity
    if (p->capacity < domain->size) {
        gf128_t* new_coeffs = safe_realloc(p->coeffs, domain->size, sizeof(gf128_t));
        if (!new_coeffs) return false;
        p->coeffs = new_coeffs;
        p->capacity = domain->size;
    }
    
    // Copy values for inverse FFT
    memcpy(p->coeffs, values, domain->size * sizeof(gf128_t));
    
    // Perform inverse FFT using inverse roots
    fft_recursive(p->coeffs, domain->size, domain->inv_elements, 1);
    
    // Scale by 1/n
    // Convert size to field element properly
    uint8_t size_bytes[16] = {0};
    size_bytes[0] = domain->size & 0xFF;
    size_bytes[1] = (domain->size >> 8) & 0xFF;
    size_bytes[2] = (domain->size >> 16) & 0xFF;
    size_bytes[3] = (domain->size >> 24) & 0xFF;
    gf128_t n = gf128_from_le(size_bytes);
    gf128_t n_inv = gf128_inv(n);
    for (size_t i = 0; i < domain->size; i++) {
        p->coeffs[i] = gf128_mul(p->coeffs[i], n_inv);
    }
    
    // Update degree
    p->degree = domain->size - 1;
    while (p->degree > 0 && gf128_is_zero(p->coeffs[p->degree])) {
        p->degree--;
    }
    
    return true;
}

/* Vanishing polynomial operations */

poly_gf128_t* compute_vanishing_polynomial(const eval_domain_t* domain) {
    if (!domain) return NULL;
    
    // For arbitrary evaluation domain H = {h_0, h_1, ..., h_{n-1}},
    // the vanishing polynomial is v_H(X) = ∏(X - h_i)
    
    // Start with (X - h_0)
    poly_gf128_t* v = poly_new(2);
    if (!v) return NULL;
    
    v->coeffs[0] = domain->elements[0];  // -h_0 = h_0 in GF(2^128)
    v->coeffs[1] = gf128_one();          // coefficient of X
    v->degree = 1;
    
    // Multiply by (X - h_i) for i = 1, ..., n-1
    for (size_t i = 1; i < domain->size; i++) {
        // Create (X - h_i)
        poly_gf128_t* linear = poly_new(2);
        if (!linear) {
            poly_free(v);
            return NULL;
        }
        
        linear->coeffs[0] = domain->elements[i];  // -h_i = h_i in GF(2^128)
        linear->coeffs[1] = gf128_one();
        linear->degree = 1;
        
        // Multiply v by (X - h_i)
        poly_gf128_t* temp = poly_new(v->degree + 2);
        if (!temp || !poly_mul(temp, v, linear)) {
            poly_free(linear);
            poly_free(v);
            poly_free(temp);
            return NULL;
        }
        
        poly_free(v);
        poly_free(linear);
        v = temp;
    }
    
    return v;
}

gf128_t vanishing_poly_eval(const eval_domain_t* domain, gf128_t x) {
    if (!domain) return gf128_zero();
    
    // v_H(x) = ∏(x - h_i) for all h_i in domain
    gf128_t result = gf128_one();
    
    for (size_t i = 0; i < domain->size; i++) {
        gf128_t factor = gf128_add(x, domain->elements[i]);  // x - h_i = x + h_i in GF(2^128)
        result = gf128_mul(result, factor);
    }
    
    return result;
}

bool poly_vanishes_on_domain(const eval_domain_t* domain, const poly_gf128_t* p) {
    if (!domain || !p) return false;
    
    // Check if p(h) = 0 for all h in domain
    for (size_t i = 0; i < domain->size; i++) {
        gf128_t val = poly_eval(p, domain->elements[i]);
        if (!gf128_is_zero(val)) {
            return false;
        }
    }
    
    return true;
}