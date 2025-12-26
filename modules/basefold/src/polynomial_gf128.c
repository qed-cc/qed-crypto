#include "polynomial_gf128.h"
#include "input_validation.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Helper function to update polynomial degree */
static void update_degree(poly_gf128_t* p) {
    if (!p || !p->coeffs) {
        p->degree = 0;
        return;
    }
    
    // Find highest non-zero coefficient
    // SECURITY FIX: Prevent underflow when capacity is 0
    if (p->capacity == 0) {
        p->degree = 0;
        return;
    }
    
    for (ssize_t i = (ssize_t)p->capacity - 1; i >= 0; i--) {
        if (!gf128_is_zero(p->coeffs[i])) {
            p->degree = (size_t)i;
            return;
        }
    }
    
    // All coefficients are zero
    p->degree = 0;
}

/* Polynomial creation and destruction */

poly_gf128_t* poly_new(size_t capacity) {
    if (capacity == 0) capacity = 1;
    
    poly_gf128_t* p = malloc(sizeof(poly_gf128_t));
    if (!p) return NULL;
    
    p->coeffs = calloc(capacity, sizeof(gf128_t));
    if (!p->coeffs) {
        free(p);
        return NULL;
    }
    
    p->degree = 0;
    p->capacity = capacity;
    return p;
}

poly_gf128_t* poly_from_coeffs(const gf128_t* coeffs, size_t num_coeffs) {
    if (!coeffs || num_coeffs == 0) return poly_zero();
    
    poly_gf128_t* p = poly_new(num_coeffs);
    if (!p) return NULL;
    
    memcpy(p->coeffs, coeffs, num_coeffs * sizeof(gf128_t));
    update_degree(p);
    return p;
}

poly_gf128_t* poly_zero(void) {
    return poly_new(1);
}

poly_gf128_t* poly_const(gf128_t c) {
    poly_gf128_t* p = poly_new(1);
    if (!p) return NULL;
    
    p->coeffs[0] = c;
    p->degree = gf128_is_zero(c) ? 0 : 0;
    return p;
}

poly_gf128_t* poly_clone(const poly_gf128_t* p) {
    if (!p) return NULL;
    return poly_from_coeffs(p->coeffs, p->capacity);
}

void poly_free(poly_gf128_t* p) {
    if (p) {
        free(p->coeffs);
        free(p);
    }
}

/* Polynomial arithmetic */

bool poly_add(poly_gf128_t* result, const poly_gf128_t* a, const poly_gf128_t* b) {
    if (!result || !a || !b) return false;
    
    size_t max_degree = (a->degree > b->degree) ? a->degree : b->degree;
    size_t required_capacity = max_degree + 1;
    
    // Ensure result has enough capacity
    if (result->capacity < required_capacity) {
        gf128_t* new_coeffs = safe_realloc(result->coeffs, required_capacity, sizeof(gf128_t));
        if (!new_coeffs) return false;
        
        // Zero out new space
        memset(new_coeffs + result->capacity, 0, 
               (required_capacity - result->capacity) * sizeof(gf128_t));
        
        result->coeffs = new_coeffs;
        result->capacity = required_capacity;
    }
    
    // Add coefficients (in GF(2^128), addition is XOR)
    size_t i;
    for (i = 0; i <= a->degree && i <= b->degree; i++) {
        result->coeffs[i] = gf128_add(a->coeffs[i], b->coeffs[i]);
    }
    
    // Copy remaining coefficients from longer polynomial
    for (; i <= a->degree; i++) {
        result->coeffs[i] = a->coeffs[i];
    }
    for (; i <= b->degree; i++) {
        result->coeffs[i] = b->coeffs[i];
    }
    
    // Clear any higher coefficients in result
    for (; i < result->capacity; i++) {
        result->coeffs[i] = gf128_zero();
    }
    
    update_degree(result);
    return true;
}

bool poly_mul(poly_gf128_t* result, const poly_gf128_t* a, const poly_gf128_t* b) {
    if (!result || !a || !b || result == a || result == b) return false;
    
    // Handle zero polynomials
    if (poly_is_zero(a) || poly_is_zero(b)) {
        memset(result->coeffs, 0, result->capacity * sizeof(gf128_t));
        result->degree = 0;
        return true;
    }
    
    // SECURITY FIX: Check for overflow in degree addition
    size_t result_degree;
    if (a->degree > SIZE_MAX - b->degree) {
        fprintf(stderr, "Error: Polynomial multiplication would cause degree overflow (deg_a=%zu, deg_b=%zu)\n", 
                a->degree, b->degree);
        fprintf(stderr, "Maximum safe polynomial degree is %zu\n", SIZE_MAX - 1);
        return false;
    }
    result_degree = a->degree + b->degree;
    
    // SECURITY FIX: Check for overflow in capacity calculation
    size_t required_capacity;
    if (result_degree == SIZE_MAX) {
        fprintf(stderr, "Error: Polynomial capacity calculation would overflow (result_degree=%zu)\n", result_degree);
        return false;
    }
    required_capacity = result_degree + 1;
    
    // Ensure result has enough capacity
    if (result->capacity < required_capacity) {
        gf128_t* new_coeffs = safe_realloc(result->coeffs, required_capacity, sizeof(gf128_t));
        if (!new_coeffs) return false;
        result->coeffs = new_coeffs;
        result->capacity = required_capacity;
    }
    
    // Clear result
    memset(result->coeffs, 0, result->capacity * sizeof(gf128_t));
    
    // SECURITY FIX: Validate polynomial degrees against capacity
    if (a->degree >= a->capacity || b->degree >= b->capacity) {
        fprintf(stderr, "Error: Invalid polynomial state detected\n");
        fprintf(stderr, "Polynomial A: degree=%zu, capacity=%zu\n", a->degree, a->capacity);
        fprintf(stderr, "Polynomial B: degree=%zu, capacity=%zu\n", b->degree, b->capacity);
        fprintf(stderr, "Polynomial degree must be less than capacity\n");
        return false;
    }
    
    // Naive polynomial multiplication
    for (size_t i = 0; i <= a->degree; i++) {
        for (size_t j = 0; j <= b->degree; j++) {
            // SECURITY FIX: Verify coefficient index is within bounds
            size_t result_idx = i + j;
            if (result_idx >= result->capacity) {
                fprintf(stderr, "Error: Coefficient index out of bounds in polynomial multiplication\n");
                fprintf(stderr, "Index: %zu, Result capacity: %zu\n", result_idx, result->capacity);
                return false;
            }
            
            gf128_t prod = gf128_mul(a->coeffs[i], b->coeffs[j]);
            result->coeffs[result_idx] = gf128_add(result->coeffs[result_idx], prod);
        }
    }
    
    result->degree = result_degree;
    return true;
}

bool poly_scalar_mul(poly_gf128_t* result, gf128_t c, const poly_gf128_t* p) {
    if (!result || !p) return false;
    
    // Handle zero scalar
    if (gf128_is_zero(c)) {
        memset(result->coeffs, 0, result->capacity * sizeof(gf128_t));
        result->degree = 0;
        return true;
    }
    
    // Ensure result has enough capacity
    if (result != p && result->capacity < p->degree + 1) {
        gf128_t* new_coeffs = safe_realloc(result->coeffs, (p->degree + 1), sizeof(gf128_t));
        if (!new_coeffs) return false;
        result->coeffs = new_coeffs;
        result->capacity = p->degree + 1;
    }
    
    // Multiply each coefficient by scalar
    for (size_t i = 0; i <= p->degree; i++) {
        result->coeffs[i] = gf128_mul(c, p->coeffs[i]);
    }
    
    // Clear higher coefficients if result has larger capacity
    for (size_t i = p->degree + 1; i < result->capacity; i++) {
        result->coeffs[i] = gf128_zero();
    }
    
    result->degree = p->degree;
    return true;
}

bool poly_div(poly_gf128_t* quotient, poly_gf128_t* remainder,
              const poly_gf128_t* dividend, const poly_gf128_t* divisor) {
    if (!dividend || !divisor || poly_is_zero(divisor)) return false;
    
    // Create temporary polynomials for computation
    poly_gf128_t* q = quotient ? quotient : poly_zero();
    poly_gf128_t* r = poly_clone(dividend);
    if (!r) return false;
    
    // Long division algorithm
    while (r->degree >= divisor->degree && !poly_is_zero(r)) {
        // Calculate leading coefficient quotient
        gf128_t lead_coeff = gf128_div(r->coeffs[r->degree], 
                                       divisor->coeffs[divisor->degree]);
        size_t shift = r->degree - divisor->degree;
        
        // Update quotient if requested
        if (quotient) {
            if (q->capacity <= shift) {
                gf128_t* new_coeffs = safe_realloc(q->coeffs, (shift + 1), sizeof(gf128_t));
                if (!new_coeffs) {
                    poly_free(r);
                    if (!quotient) poly_free(q);
                    return false;
                }
                // Zero out new space
                memset(new_coeffs + q->capacity, 0, 
                       (shift + 1 - q->capacity) * sizeof(gf128_t));
                q->coeffs = new_coeffs;
                q->capacity = shift + 1;
            }
            q->coeffs[shift] = lead_coeff;
            if (shift > q->degree) q->degree = shift;
        }
        
        // Subtract divisor * lead_coeff * X^shift from remainder
        for (size_t i = 0; i <= divisor->degree; i++) {
            gf128_t term = gf128_mul(lead_coeff, divisor->coeffs[i]);
            r->coeffs[i + shift] = gf128_add(r->coeffs[i + shift], term);
        }
        
        update_degree(r);
    }
    
    // Copy remainder if requested
    if (remainder) {
        if (remainder->capacity < r->capacity) {
            gf128_t* new_coeffs = safe_realloc(remainder->coeffs, r->capacity, sizeof(gf128_t));
            if (!new_coeffs) {
                poly_free(r);
                if (!quotient) poly_free(q);
                return false;
            }
            remainder->coeffs = new_coeffs;
            remainder->capacity = r->capacity;
        }
        memcpy(remainder->coeffs, r->coeffs, r->capacity * sizeof(gf128_t));
        remainder->degree = r->degree;
    }
    
    poly_free(r);
    if (!quotient) poly_free(q);
    
    return true;
}

/* Polynomial evaluation */

gf128_t poly_eval(const poly_gf128_t* p, gf128_t x) {
    if (!p || poly_is_zero(p)) return gf128_zero();
    
    // Horner's method for efficient evaluation
    gf128_t result = p->coeffs[p->degree];
    
    for (ssize_t i = p->degree - 1; i >= 0; i--) {
        result = gf128_mul(result, x);
        result = gf128_add(result, p->coeffs[i]);
    }
    
    return result;
}

bool poly_multi_eval(const poly_gf128_t* p, const gf128_t* points,
                     gf128_t* values, size_t num_points) {
    if (!p || !points || !values) return false;
    
    for (size_t i = 0; i < num_points; i++) {
        values[i] = poly_eval(p, points[i]);
    }
    
    return true;
}

/* Polynomial interpolation */

poly_gf128_t* poly_interpolate(const gf128_t* points, const gf128_t* values,
                               size_t num_points) {
    if (!points || !values || num_points == 0) return NULL;
    
    // Lagrange interpolation
    poly_gf128_t* result = poly_zero();
    if (!result) return NULL;
    
    for (size_t i = 0; i < num_points; i++) {
        // Compute Lagrange basis polynomial L_i(X)
        poly_gf128_t* li = poly_const(gf128_one());
        if (!li) {
            poly_free(result);
            return NULL;
        }
        
        for (size_t j = 0; j < num_points; j++) {
            if (i == j) continue;
            
            // L_i(X) *= (X - points[j]) / (points[i] - points[j])
            poly_gf128_t* factor = poly_new(2);
            if (!factor) {
                poly_free(li);
                poly_free(result);
                return NULL;
            }
            
            // (X - points[j])
            factor->coeffs[0] = points[j];  // -points[j] = points[j] in GF(2^128)
            factor->coeffs[1] = gf128_one();
            factor->degree = 1;
            
            // Multiply by 1/(points[i] - points[j])
            gf128_t denom = gf128_add(points[i], points[j]);
            gf128_t inv_denom = gf128_inv(denom);
            
            poly_gf128_t* temp = poly_new(li->degree + 2);
            if (!temp || !poly_mul(temp, li, factor)) {
                poly_free(factor);
                poly_free(li);
                poly_free(result);
                poly_free(temp);
                return NULL;
            }
            
            poly_free(li);
            li = temp;
            
            if (!poly_scalar_mul(li, inv_denom, li)) {
                poly_free(factor);
                poly_free(li);
                poly_free(result);
                return NULL;
            }
            
            poly_free(factor);
        }
        
        // Add values[i] * L_i(X) to result
        if (!poly_scalar_mul(li, values[i], li) ||
            !poly_add(result, result, li)) {
            poly_free(li);
            poly_free(result);
            return NULL;
        }
        
        poly_free(li);
    }
    
    return result;
}

/* Utility functions */

bool poly_is_zero(const poly_gf128_t* p) {
    if (!p || !p->coeffs) return true;
    
    for (size_t i = 0; i <= p->degree; i++) {
        if (!gf128_is_zero(p->coeffs[i])) return false;
    }
    
    return true;
}

void poly_print(const poly_gf128_t* p, const char* name) {
    if (!p) {
        printf("%s: NULL\n", name ? name : "poly");
        return;
    }
    
    printf("%s: ", name ? name : "poly");
    
    if (poly_is_zero(p)) {
        printf("0\n");
        return;
    }
    
    bool first = true;
    for (ssize_t i = p->degree; i >= 0; i--) {
        if (gf128_is_zero(p->coeffs[i])) continue;
        
        if (!first) printf(" + ");
        first = false;
        
        // Print coefficient (just show if it's 1 or not for simplicity)
        if (i == 0) {
            printf("{%016lx,%016lx}", p->coeffs[i].hi, p->coeffs[i].lo);
        } else if (i == 1) {
            if (gf128_eq(p->coeffs[i], gf128_one())) {
                printf("X");
            } else {
                printf("{%016lx,%016lx}*X", p->coeffs[i].hi, p->coeffs[i].lo);
            }
        } else {
            if (gf128_eq(p->coeffs[i], gf128_one())) {
                printf("X^%zd", i);
            } else {
                printf("{%016lx,%016lx}*X^%zd", p->coeffs[i].hi, p->coeffs[i].lo, i);
            }
        }
    }
    
    printf(" (degree %zu)\n", p->degree);
}