#include "vanishing_poly.h"
#include "prg.h"
#include <stdlib.h>
#include <string.h>

#ifdef __x86_64__
#include <immintrin.h>
#endif

vanishing_poly_t* vanishing_poly_create(size_t num_vars) {
    vanishing_poly_t* v = malloc(sizeof(vanishing_poly_t));
    if (!v) return NULL;
    
    v->num_vars = num_vars;
    return v;
}

void vanishing_poly_free(vanishing_poly_t* v) {
    free(v);
}

gf128_t vanishing_hypercube_eval(
    const vanishing_poly_t* v,
    const gf128_t* point) {
    
    if (!v || !point) return gf128_zero();
    
    gf128_t result = gf128_one();
    
    // Compute ∏xi(xi - 1) for all variables
    for (size_t i = 0; i < v->num_vars; i++) {
        // xi * (xi - 1) = xi² - xi
        // In GF(2^128), -1 = 1, so xi - 1 = xi + 1
        gf128_t xi = point[i];
        gf128_t xi_plus_1 = gf128_add(xi, gf128_one());
        gf128_t factor = gf128_mul(xi, xi_plus_1);
        result = gf128_mul(result, factor);
    }
    
    return result;
}

bool is_boolean_point(const gf128_t* point, size_t num_vars) {
    if (!point) return false;
    
    for (size_t i = 0; i < num_vars; i++) {
        // Check if xi is 0 or 1
        if (!gf128_is_zero(point[i]) && !gf128_eq(point[i], gf128_one())) {
            return false;
        }
    }
    return true;
}

gf128_t vanishing_times_random_eval(
    const vanishing_poly_t* v,
    const gf128_t* point,
    const uint8_t seed[16],
    size_t degree) {
    
    if (!v || !point || !seed) return gf128_zero();
    
    // First compute v_H(point)
    gf128_t vh_eval = vanishing_hypercube_eval(v, point);
    
    // If v_H(point) = 0, the product is 0 regardless of r(X)
    if (gf128_is_zero(vh_eval)) {
        return gf128_zero();
    }
    
    // Initialize PRG with seed
    prg_init(seed);
    
    // Otherwise, we need to evaluate r(point)
    // For a random polynomial of given degree, we generate coefficients
    // and evaluate using Horner's method
    
    // For multivariate case, this is more complex
    // For now, use a simple approach - generate a univariate polynomial
    // and evaluate it at the first coordinate
    
    gf128_t r_eval = gf128_zero();
    gf128_t power = gf128_one();
    
    for (size_t i = 0; i <= degree; i++) {
        // Generate random coefficient
        gf128_t coeff;
#ifdef __x86_64__
        __m128i coeff_m = prg_next();
        coeff.lo = _mm_extract_epi64(coeff_m, 0);
        coeff.hi = _mm_extract_epi64(coeff_m, 1);
#else
        uint8_t coeff_bytes[16];
        prg_next(coeff_bytes);
        coeff = gf128_from_bytes(coeff_bytes);
#endif
        
        // Add coeff * x^i to result
        r_eval = gf128_add(r_eval, gf128_mul(coeff, power));
        
        // Update power for next iteration
        if (i < degree) {
            power = gf128_mul(power, point[0]);  // Use first coordinate
        }
    }
    
    // Return v_H(point) * r(point)
    return gf128_mul(vh_eval, r_eval);
}