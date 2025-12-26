#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "gate_sumcheck_multilinear.h"
#include "gf128.h"

// Helper to create gf128 from int
static inline gf128_t gf128_from_int(int x) {
    gf128_t result = {0, (uint64_t)x};
    return result;
}

void test_interpolation(void) {
    printf("=== Testing Polynomial Interpolation ===\n\n");
    
    // Test case: We have evaluations at 0,1,2,3
    // Let's say f(0)=1, f(1)=2, f(2)=3, f(3)=4
    gf128_t evals[4];
    evals[0] = gf128_from_int(1);
    evals[1] = gf128_from_int(2);
    evals[2] = gf128_from_int(3);
    evals[3] = gf128_from_int(4);
    
    printf("Original evaluations:\n");
    for (int i = 0; i < 4; i++) {
        printf("  f(%d) = %lu\n", i, evals[i].lo);
    }
    
    // Compute coefficients using the formula from compute_round_polynomial_ml
    gf128_t g0 = evals[0];
    gf128_t g1 = gf128_add(evals[0], evals[1]);
    gf128_t g2 = gf128_add(evals[0], evals[2]);
    gf128_t g3 = gf128_add(gf128_add(evals[0], evals[1]), 
                          gf128_add(evals[2], evals[3]));
    
    printf("\nComputed coefficients:\n");
    printf("  g0 = %lu\n", g0.lo);
    printf("  g1 = %lu\n", g1.lo);
    printf("  g2 = %lu\n", g2.lo);
    printf("  g3 = %lu\n", g3.lo);
    
    // Verify by evaluating polynomial at 0,1,2,3
    printf("\nVerifying polynomial evaluation:\n");
    for (int x = 0; x < 4; x++) {
        gf128_t x_val = gf128_from_int(x);
        gf128_t result = g0;
        
        // Add g1*x
        result = gf128_add(result, gf128_mul(g1, x_val));
        
        // Add g2*x^2
        gf128_t x2 = gf128_mul(x_val, x_val);
        result = gf128_add(result, gf128_mul(g2, x2));
        
        // Add g3*x^3
        gf128_t x3 = gf128_mul(x2, x_val);
        result = gf128_add(result, gf128_mul(g3, x3));
        
        printf("  p(%d) = %lu (expected %lu)\n", x, result.lo, evals[x].lo);
    }
    
    // In GF(2^128), things work differently
    printf("\nNote: In GF(2^128):\n");
    printf("  1 + 2 = %lu (not 3!)\n", gf128_add(gf128_from_int(1), gf128_from_int(2)).lo);
    printf("  2 * 2 = %lu\n", gf128_mul(gf128_from_int(2), gf128_from_int(2)).lo);
    printf("  3 * 3 = %lu\n", gf128_mul(gf128_from_int(3), gf128_from_int(3)).lo);
}

void test_round_computation(void) {
    printf("\n=== Testing Round Computation ===\n\n");
    
    // Simple case: constant zero polynomial
    // This should give g(X) = 0
    
    printf("If F(x) = 0 for all x, then:\n");
    printf("  g(X) = sum over remaining vars of F(...,X,...) = 0\n");
    printf("  So g(0) = 0, g(1) = 0\n");
    printf("  And g(0) + g(1) = 0\n");
    
    // The issue might be that the interpolation assumes we're evaluating
    // at 0,1,2,3 but we only need 0,1 for sumcheck
}

int main(void) {
    test_interpolation();
    test_round_computation();
    return 0;
}