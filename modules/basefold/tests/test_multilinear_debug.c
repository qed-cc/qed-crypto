#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "multilinear.h"
#include "gf128.h"

// Helper functions for tests
static inline gf128_t gf128_from_int(int x) {
    gf128_t result = {0, (uint64_t)x};
    return result;
}

static inline bool gf128_equal(gf128_t a, gf128_t b) {
    return gf128_eq(a, b);
}

void debug_multilinear_eval(void) {
    printf("=== Debug Multilinear Evaluation ===\n\n");
    
    // Create simple 2-variable polynomial
    // f(x,y) with evaluations at (0,0), (0,1), (1,0), (1,1)
    multilinear_poly_t* poly = multilinear_create(2);
    
    // Set evaluations: f(0,0)=1, f(0,1)=2, f(1,0)=3, f(1,1)=4
    poly->evaluations[0] = gf128_from_int(1);  // (0,0)
    poly->evaluations[1] = gf128_from_int(2);  // (0,1)
    poly->evaluations[2] = gf128_from_int(3);  // (1,0)
    poly->evaluations[3] = gf128_from_int(4);  // (1,1)
    
    printf("Polynomial evaluations:\n");
    multilinear_print(poly, "f");
    
    // Test evaluation at boolean points
    printf("\nTesting boolean evaluations:\n");
    
    gf128_t point00[2] = {gf128_zero(), gf128_zero()};
    gf128_t result00 = multilinear_eval(poly, point00);
    printf("f(0,0) = %lu (expected 1)\n", result00.lo);
    
    gf128_t point01[2] = {gf128_zero(), gf128_one()};
    gf128_t result01 = multilinear_eval(poly, point01);
    printf("f(0,1) = %lu (expected 2)\n", result01.lo);
    
    gf128_t point10[2] = {gf128_one(), gf128_zero()};
    gf128_t result10 = multilinear_eval(poly, point10);
    printf("f(1,0) = %lu (expected 3)\n", result10.lo);
    
    gf128_t point11[2] = {gf128_one(), gf128_one()};
    gf128_t result11 = multilinear_eval(poly, point11);
    printf("f(1,1) = %lu (expected 4)\n", result11.lo);
    
    // Let's trace through the evaluation algorithm for f(0,1)
    printf("\nDetailed trace for f(0,1):\n");
    printf("Initial evaluations: [1, 2, 3, 4]\n");
    
    // First variable (x0 = 0)
    printf("Variable 0, value = 0:\n");
    printf("  Interpolate pairs:\n");
    printf("    (0,0): (1-0)*1 + 0*3 = 1\n");
    printf("    (0,1): (1-0)*2 + 0*4 = 2\n");
    printf("  After variable 0: [1, 2]\n");
    
    // Second variable (x1 = 1)
    printf("Variable 1, value = 1:\n");
    printf("  Interpolate:\n");
    printf("    (1-1)*1 + 1*2 = 0 + 2 = 2\n");
    printf("  Result: 2\n");
    
    multilinear_free(poly);
}

void debug_index_conversion(void) {
    printf("\n=== Debug Index Conversion ===\n");
    
    // Test for 3 variables
    printf("3-variable index conversions:\n");
    for (size_t i = 0; i < 8; i++) {
        gf128_t vec[3];
        multilinear_index_to_vec(i, vec, 3);
        
        printf("Index %zu -> (", i);
        for (size_t j = 0; j < 3; j++) {
            printf("%d", !gf128_is_zero(vec[j]));
            if (j < 2) printf(",");
        }
        printf(")\n");
    }
}

int main(void) {
    debug_multilinear_eval();
    debug_index_conversion();
    return 0;
}