#include "multilinear.h"
#include "basefold_trace.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

#ifdef __x86_64__
#include <immintrin.h>
#endif

/* Core operations */

multilinear_poly_t* multilinear_create(size_t num_vars) {
    // SECURITY FIX: More conservative bounds to prevent overflow
    // On 32-bit systems, size_t is 32 bits, so we need stricter limits
    size_t max_vars = (sizeof(size_t) == 4) ? 29 : 30;  // 2^29 on 32-bit, 2^30 on 64-bit
    
    if (num_vars > max_vars) {  
        fprintf(stderr, "Error: Too many variables for multilinear polynomial (%zu variables)\n", num_vars);
        fprintf(stderr, "Maximum safe variables: %zu (prevents memory overflow)\n", max_vars);
        fprintf(stderr, "This would require %llu bytes of memory\n", 
                (num_vars < 64) ? ((1ULL << num_vars) * sizeof(gf128_t)) : SIZE_MAX);
        return NULL;
    }
    
    multilinear_poly_t* poly = malloc(sizeof(multilinear_poly_t));
    if (!poly) return NULL;
    
    poly->num_vars = num_vars;
    // SECURITY FIX: Additional check to ensure shift doesn't overflow
    if (num_vars >= 64) {
        fprintf(stderr, "Error: Cannot create multilinear polynomial with %zu variables\n", num_vars);
        fprintf(stderr, "Bit shift operations are undefined for shifts >= 64\n");
        free(poly);
        return NULL;
    }
    poly->padded_size = 1ULL << num_vars;
    
    // Allocate aligned memory for SIMD operations
    if (posix_memalign((void**)&poly->evaluations, 32, 
                       poly->padded_size * sizeof(gf128_t)) != 0) {
        free(poly);
        return NULL;
    }
    
    // Initialize to zero
    memset(poly->evaluations, 0, poly->padded_size * sizeof(gf128_t));
    
    return poly;
}

multilinear_poly_t* multilinear_from_evaluations(const gf128_t* evaluations, size_t num_vars) {
    multilinear_poly_t* poly = multilinear_create(num_vars);
    if (!poly) return NULL;
    
    memcpy(poly->evaluations, evaluations, poly->padded_size * sizeof(gf128_t));
    return poly;
}

void multilinear_free(multilinear_poly_t* poly) {
    if (poly) {
        free(poly->evaluations);
        free(poly);
    }
}

multilinear_poly_t* multilinear_clone(const multilinear_poly_t* poly) {
    if (!poly) return NULL;
    return multilinear_from_evaluations(poly->evaluations, poly->num_vars);
}

/* Evaluation */

gf128_t multilinear_eval(const multilinear_poly_t* poly, const gf128_t* point) {
    if (!poly || !point) {
        fprintf(stderr, "Error: NULL polynomial or evaluation point in multilinear_eval\n");
        return gf128_zero();
    }
    
    // SECURITY FIX: Validate polynomial parameters
    if (poly->num_vars == 0) {
        fprintf(stderr, "Error: Cannot evaluate polynomial with 0 variables\n");
        return gf128_zero();
    }
    
    if (poly->num_vars >= 64) {
        fprintf(stderr, "Error: Too many variables (%zu) for safe evaluation\n", poly->num_vars);
        return gf128_zero();
    }
    
    if (poly->padded_size != (1ULL << poly->num_vars)) {
        fprintf(stderr, "Error: Inconsistent polynomial size (expected %llu, got %zu)\n", 
                (1ULL << poly->num_vars), poly->padded_size);
        return gf128_zero();
    }
    
    // SECURITY NOTE: We cannot validate the point array size here since it's passed as a pointer
    // The caller must ensure point has exactly num_vars elements
    
    // Dynamic programming approach
    // We iteratively reduce the number of variables
    size_t n = poly->padded_size;
    
    // Allocate working arrays
    gf128_t* current = malloc(n * sizeof(gf128_t));
    gf128_t* next = malloc(n * sizeof(gf128_t));
    if (!current || !next) {
        free(current);
        free(next);
        return gf128_zero();
    }
    
    // Initialize with polynomial evaluations
    memcpy(current, poly->evaluations, n * sizeof(gf128_t));
    
    // For each variable
    for (size_t var = 0; var < poly->num_vars; var++) {
        // SECURITY FIX: Validate evaluation point for security-critical applications
        // In zero-knowledge protocols, evaluation points should come from transcript
        // and be properly validated to prevent manipulation attacks
        gf128_t eval_point = point[var];
        
        // Check for potential problematic values that could break soundness
        // Note: In boolean hypercube evaluation, points should typically be non-zero/non-one
        // for security, but we allow all valid GF(2^128) elements here
        if (gf128_is_zero(eval_point) || gf128_eq(eval_point, gf128_one())) {
            // WARNING: Boolean evaluation points (0,1) may reduce security in some protocols
            // This is logged but not blocked, as some protocols may legitimately use these values
            static bool warned = false;
            if (!warned) {
                fprintf(stderr, "Warning: Using boolean evaluation point in multilinear evaluation\n");
                fprintf(stderr, "This may reduce security in zero-knowledge protocols\n");
                warned = true;
            }
        }
        
        size_t stride = 1ULL << (poly->num_vars - var - 1);
        
        // SECURITY FIX: Additional bounds check for stride calculation
        if (poly->num_vars < var + 1) {
            fprintf(stderr, "Error: Invalid variable index %zu in polynomial with %zu variables\n", 
                    var, poly->num_vars);
            free(current);
            free(next);
            return gf128_zero();
        }
        
        // Interpolate and evaluate at point[var]
        for (size_t i = 0; i < stride; i++) {
            // Get evaluations at xi = 0 and xi = 1
            gf128_t f0 = current[2*i];
            gf128_t f1 = current[2*i + 1];
            
            // Linear interpolation: f(r) = (1-r)*f(0) + r*f(1)
            // In GF(2^128): 1-r = 1+r
            gf128_t one_minus_r = gf128_add(gf128_one(), eval_point);
            
            next[i] = gf128_add(
                gf128_mul(one_minus_r, f0),
                gf128_mul(eval_point, f1)
            );
        }
        
        // Swap buffers
        gf128_t* temp = current;
        current = next;
        next = temp;
    }
    
    gf128_t result = current[0];
    free(current);
    free(next);
    return result;
}

/* Memoization support */

multilinear_memo_t* multilinear_memo_create(size_t num_vars) {
    multilinear_memo_t* memo = malloc(sizeof(multilinear_memo_t));
    if (!memo) return NULL;
    
    memo->num_vars = num_vars;
    memo->table = malloc(num_vars * sizeof(gf128_t*));
    memo->initialized = calloc(num_vars, sizeof(bool));
    
    if (!memo->table || !memo->initialized) {
        free(memo->table);
        free(memo->initialized);
        free(memo);
        return NULL;
    }
    
    // Allocate sub-tables
    for (size_t i = 0; i < num_vars; i++) {
        size_t size = 1ULL << (num_vars - i);
        memo->table[i] = malloc(size * sizeof(gf128_t));
        if (!memo->table[i]) {
            // Clean up on failure
            for (size_t j = 0; j < i; j++) {
                free(memo->table[j]);
            }
            free(memo->table);
            free(memo->initialized);
            free(memo);
            return NULL;
        }
    }
    
    return memo;
}

void multilinear_memo_reset(multilinear_memo_t* memo) {
    if (memo) {
        memset(memo->initialized, 0, memo->num_vars * sizeof(bool));
    }
}

void multilinear_memo_free(multilinear_memo_t* memo) {
    if (memo) {
        for (size_t i = 0; i < memo->num_vars; i++) {
            free(memo->table[i]);
        }
        free(memo->table);
        free(memo->initialized);
        free(memo);
    }
}

gf128_t multilinear_eval_memoized(
    const multilinear_poly_t* poly,
    const gf128_t* point,
    multilinear_memo_t* memo) {
    
    if (!poly || !point || !memo || memo->num_vars != poly->num_vars) {
        return multilinear_eval(poly, point);  // Fall back to non-memoized
    }
    
    // TODO: Implement memoized evaluation for repeated evaluations
    // For now, just use regular evaluation
    return multilinear_eval(poly, point);
}

/* Arithmetic operations */

bool multilinear_add(
    multilinear_poly_t* result,
    const multilinear_poly_t* a,
    const multilinear_poly_t* b) {
    
    if (!result || !a || !b) return false;
    if (a->num_vars != b->num_vars || result->num_vars != a->num_vars) return false;
    
    // Add evaluations pointwise
    for (size_t i = 0; i < a->padded_size; i++) {
        result->evaluations[i] = gf128_add(a->evaluations[i], b->evaluations[i]);
    }
    
    return true;
}

multilinear_poly_t* multilinear_mul(
    const multilinear_poly_t* a,
    const multilinear_poly_t* b) {
    
    if (!a || !b) return NULL;
    
    // SECURITY FIX: Check for overflow in variable addition
    size_t result_vars;
    if (a->num_vars > SIZE_MAX - b->num_vars) {
        fprintf(stderr, "Error: Multilinear polynomial multiplication would cause variable overflow\n");
        fprintf(stderr, "Polynomial A variables: %zu, Polynomial B variables: %zu\n", 
                a->num_vars, b->num_vars);
        fprintf(stderr, "Total would exceed maximum size_t value\n");
        return NULL;
    }
    result_vars = a->num_vars + b->num_vars;
    
    multilinear_poly_t* result = multilinear_create(result_vars);
    if (!result) return NULL;
    
    // SECURITY FIX: Validate shift operations won't overflow
    if (a->num_vars >= 64) {
        fprintf(stderr, "Error: Cannot multiply multilinear polynomial with %zu variables\n", a->num_vars);
        fprintf(stderr, "Bit shift operations are undefined for shifts >= 64\n");
        multilinear_free(result);
        return NULL;
    }
    
    // For each evaluation point in the result
    for (size_t i = 0; i < result->padded_size; i++) {
        // Split index into indices for a and b
        size_t idx_a = i & ((1ULL << a->num_vars) - 1);
        size_t idx_b = i >> a->num_vars;
        
        // Multiply corresponding evaluations
        result->evaluations[i] = gf128_mul(
            a->evaluations[idx_a],
            b->evaluations[idx_b]
        );
    }
    
    return result;
}

bool multilinear_scale(
    multilinear_poly_t* result,
    const multilinear_poly_t* poly,
    gf128_t scalar) {
    
    if (!result || !poly) return false;
    if (result->num_vars != poly->num_vars) return false;
    
    for (size_t i = 0; i < poly->padded_size; i++) {
        result->evaluations[i] = gf128_mul(poly->evaluations[i], scalar);
    }
    
    return true;
}

/* Utility functions */

void multilinear_index_to_vec(size_t index, gf128_t* vec, size_t num_vars) {
    // SECURITY FIX: Validate parameters to prevent buffer overflow
    if (!vec) {
        fprintf(stderr, "Error: NULL vector pointer in multilinear_index_to_vec\n");
        return;
    }
    
    if (num_vars >= 64) {
        fprintf(stderr, "Error: Too many variables (%zu) for safe bit operations\n", num_vars);
        fprintf(stderr, "Bit shift operations are undefined for shifts >= 64\n");
        return;
    }
    
    // SECURITY FIX: Check if index is within valid range
    if (num_vars > 0 && index >= (1ULL << num_vars)) {
        fprintf(stderr, "Error: Index %zu exceeds maximum for %zu variables (max: %llu)\n", 
                index, num_vars, (1ULL << num_vars) - 1);
        return;
    }
    
    for (size_t i = 0; i < num_vars; i++) {
        vec[i] = (index & (1ULL << i)) ? gf128_one() : gf128_zero();
    }
}

size_t multilinear_vec_to_index(const gf128_t* vec, size_t num_vars) {
    // SECURITY FIX: Validate parameters to prevent integer overflow
    if (!vec) {
        fprintf(stderr, "Error: NULL vector pointer in multilinear_vec_to_index\n");
        return 0;
    }
    
    if (num_vars >= 64) {
        fprintf(stderr, "Error: Too many variables (%zu) for safe bit operations\n", num_vars);
        fprintf(stderr, "Bit shift operations are undefined for shifts >= 64\n");
        return 0;
    }
    
    size_t index = 0;
    for (size_t i = 0; i < num_vars; i++) {
        if (!gf128_is_zero(vec[i])) {
            // SECURITY FIX: Additional check to prevent shift overflow (redundant but safe)
            if (i >= 64) {
                fprintf(stderr, "Error: Variable index %zu would cause shift overflow\n", i);
                return 0;
            }
            index |= (1ULL << i);
        }
    }
    return index;
}

bool multilinear_is_zero(const multilinear_poly_t* poly) {
    if (!poly) return true;
    
    for (size_t i = 0; i < poly->padded_size; i++) {
        if (!gf128_is_zero(poly->evaluations[i])) {
            return false;
        }
    }
    return true;
}

void multilinear_print(const multilinear_poly_t* poly, const char* name) {
    if (!poly) return;
    
    printf("Multilinear polynomial %s (%zu vars):\n", 
           name ? name : "unnamed", poly->num_vars);
    
    // Print up to 16 evaluations
    size_t limit = poly->padded_size < 16 ? poly->padded_size : 16;
    
    for (size_t i = 0; i < limit; i++) {
        printf("  f(");
        for (size_t j = 0; j < poly->num_vars; j++) {
            printf("%d", (int)((i >> j) & 1));
            if (j < poly->num_vars - 1) printf(",");
        }
        printf(") = %016lx%016lx\n", 
               poly->evaluations[i].hi, poly->evaluations[i].lo);
    }
    
    if (poly->padded_size > 16) {
        printf("  ... (%zu more evaluations)\n", poly->padded_size - 16);
    }
}

/* Trace conversion */

multilinear_poly_t* trace_column_to_multilinear(
    const basefold_trace_t* trace,
    size_t column_idx) {
    
    if (!trace || column_idx >= 4) return NULL;
    
    // Calculate log2(padded_size)
    size_t log_padded_size = 0;
    size_t temp = trace->padded_size;
    while (temp > 1) {
        log_padded_size++;
        temp >>= 1;
    }
    
    // Create polynomial with log2(padded_size) variables
    multilinear_poly_t* poly = multilinear_create(log_padded_size);
    if (!poly) return NULL;
    
    // Copy column data
    // Trace is now in column-major format after transposition in main.c
    size_t offset = column_idx * trace->padded_size;
    
    // Convert from __m128i to gf128_t
#ifdef __x86_64__
    for (size_t i = 0; i < trace->padded_size; i++) {
        __m128i elem = trace->field_elements[offset + i];
        // Extract hi and lo parts from __m128i
        poly->evaluations[i].lo = _mm_extract_epi64(elem, 0);
        poly->evaluations[i].hi = _mm_extract_epi64(elem, 1);
    }
#else
    // For non-x86_64, field_elements is array of bytes
    for (size_t i = 0; i < trace->padded_size; i++) {
        uint8_t* elem_bytes = &trace->field_elements[(offset + i) * 16];
        // Convert 16 bytes to gf128_t (assuming little-endian storage)
        memcpy(&poly->evaluations[i].lo, elem_bytes, 8);
        memcpy(&poly->evaluations[i].hi, elem_bytes + 8, 8);
    }
#endif
    
    return poly;
}