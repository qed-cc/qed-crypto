#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "vanishing_poly.h"
#include "gf128.h"

// Helper to create gf128 from int
static inline gf128_t gf128_from_int(int x) {
    gf128_t result = {0, (uint64_t)x};
    return result;
}

// Test basic vanishing polynomial evaluation
static void test_vanishing_eval_boolean(void) {
    printf("Testing vanishing polynomial on boolean points...\n");
    
    // Create vanishing polynomial for 3 variables
    vanishing_poly_t* v = vanishing_poly_create(3);
    assert(v != NULL);
    
    // Test that it vanishes on all boolean points
    for (int i = 0; i < 8; i++) {
        gf128_t point[3];
        point[0] = (i & 1) ? gf128_one() : gf128_zero();
        point[1] = (i & 2) ? gf128_one() : gf128_zero();
        point[2] = (i & 4) ? gf128_one() : gf128_zero();
        
        gf128_t result = vanishing_hypercube_eval(v, point);
        
        printf("  v_H(%d,%d,%d) = %016lx%016lx (should be 0)\n",
               (i & 1), (i & 2) >> 1, (i & 4) >> 2,
               result.hi, result.lo);
        
        assert(gf128_is_zero(result));
    }
    
    vanishing_poly_free(v);
    printf("  ✓ Vanishing on boolean points test passed\n");
}

// Test evaluation at non-boolean points
static void test_vanishing_eval_general(void) {
    printf("Testing vanishing polynomial on non-boolean points...\n");
    
    vanishing_poly_t* v = vanishing_poly_create(2);
    
    // Test at point (2, 3)
    gf128_t point[2] = {gf128_from_int(2), gf128_from_int(3)};
    gf128_t result = vanishing_hypercube_eval(v, point);
    
    // v_H(2,3) = (2)(2+1) * (3)(3+1) = (2)(3) * (3)(2) = 6 * 6 = 36
    // But in GF(2^128): 2+1=3, 3+1=2, so it's 2*3 * 3*2 = 6*6
    // In GF(2^128), multiplication is different
    
    printf("  v_H(2,3) = %016lx%016lx (should be non-zero)\n",
           result.hi, result.lo);
    assert(!gf128_is_zero(result));
    
    // Test at point (0, 3)
    gf128_t point2[2] = {gf128_zero(), gf128_from_int(3)};
    gf128_t result2 = vanishing_hypercube_eval(v, point2);
    
    // v_H(0,3) = (0)(0+1) * (3)(3+1) = 0 * (3)(2) = 0
    printf("  v_H(0,3) = %016lx%016lx (should be 0)\n",
           result2.hi, result2.lo);
    assert(gf128_is_zero(result2));
    
    vanishing_poly_free(v);
    printf("  ✓ General evaluation test passed\n");
}

// Test is_boolean_point function
static void test_is_boolean_point(void) {
    printf("Testing is_boolean_point function...\n");
    
    // Test boolean points
    gf128_t bool_point[3] = {gf128_zero(), gf128_one(), gf128_zero()};
    assert(is_boolean_point(bool_point, 3));
    
    gf128_t bool_point2[3] = {gf128_one(), gf128_one(), gf128_one()};
    assert(is_boolean_point(bool_point2, 3));
    
    // Test non-boolean points
    gf128_t non_bool[3] = {gf128_from_int(2), gf128_one(), gf128_zero()};
    assert(!is_boolean_point(non_bool, 3));
    
    gf128_t non_bool2[3] = {gf128_zero(), gf128_from_int(5), gf128_one()};
    assert(!is_boolean_point(non_bool2, 3));
    
    printf("  ✓ Boolean point detection test passed\n");
}

// Test edge cases
static void test_edge_cases(void) {
    printf("Testing edge cases...\n");
    
    // Test with 0 variables
    vanishing_poly_t* v0 = vanishing_poly_create(0);
    gf128_t dummy[1];
    gf128_t result = vanishing_hypercube_eval(v0, dummy);
    // With 0 variables, the product is empty, so result should be 1
    assert(gf128_eq(result, gf128_one()));
    vanishing_poly_free(v0);
    
    // Test with 1 variable
    vanishing_poly_t* v1 = vanishing_poly_create(1);
    gf128_t point_0[1] = {gf128_zero()};
    gf128_t point_1[1] = {gf128_one()};
    gf128_t point_2[1] = {gf128_from_int(2)};
    
    assert(gf128_is_zero(vanishing_hypercube_eval(v1, point_0)));
    assert(gf128_is_zero(vanishing_hypercube_eval(v1, point_1)));
    assert(!gf128_is_zero(vanishing_hypercube_eval(v1, point_2)));
    
    vanishing_poly_free(v1);
    
    printf("  ✓ Edge cases test passed\n");
}

// Test performance with larger number of variables
static void test_performance(void) {
    printf("Testing performance with many variables...\n");
    
    for (size_t n = 4; n <= 20; n += 4) {
        vanishing_poly_t* v = vanishing_poly_create(n);
        
        // Create a random non-boolean point
        gf128_t* point = malloc(n * sizeof(gf128_t));
        for (size_t i = 0; i < n; i++) {
            point[i] = gf128_from_int(i + 2);  // All non-boolean
        }
        
        gf128_t result = vanishing_hypercube_eval(v, point);
        printf("  %zu variables: v_H evaluated to %016lx%016lx\n",
               n, result.hi, result.lo);
        assert(!gf128_is_zero(result));
        
        free(point);
        vanishing_poly_free(v);
    }
    
    printf("  ✓ Performance test passed\n");
}

int main(void) {
    printf("=== Vanishing Polynomial Tests ===\n\n");
    
    test_vanishing_eval_boolean();
    test_vanishing_eval_general();
    test_is_boolean_point();
    test_edge_cases();
    test_performance();
    
    printf("\n✅ All vanishing polynomial tests passed!\n");
    return 0;
}