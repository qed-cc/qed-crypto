#include <stdio.h>
#include <assert.h>
#include "polynomial_gf128.h"

void test_polynomial_basic() {
    printf("Testing basic polynomial operations...\n");
    
    // Test creation
    poly_gf128_t* p1 = poly_new(10);
    assert(p1 != NULL);
    assert(p1->capacity == 10);
    assert(p1->degree == 0);
    
    // Test constant polynomial
    gf128_t one = gf128_one();
    poly_gf128_t* p2 = poly_const(one);
    assert(p2 != NULL);
    assert(gf128_eq(p2->coeffs[0], one));
    
    // Test polynomial from coefficients
    gf128_t coeffs[3] = {
        gf128_one(),
        gf128_from_le((uint8_t*)"\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"),
        gf128_from_le((uint8_t*)"\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")
    };
    poly_gf128_t* p3 = poly_from_coeffs(coeffs, 3);
    assert(p3 != NULL);
    assert(p3->degree == 2);
    
    poly_free(p1);
    poly_free(p2);
    poly_free(p3);
    
    printf("Basic tests passed!\n");
}

void test_polynomial_arithmetic() {
    printf("Testing polynomial arithmetic...\n");
    
    // Create two simple polynomials
    // p1(X) = 1 + X
    gf128_t coeffs1[2] = { gf128_one(), gf128_one() };
    poly_gf128_t* p1 = poly_from_coeffs(coeffs1, 2);
    
    // p2(X) = 1 + X + X^2
    gf128_t coeffs2[3] = { gf128_one(), gf128_one(), gf128_one() };
    poly_gf128_t* p2 = poly_from_coeffs(coeffs2, 3);
    
    // Test addition: p1 + p2 = X^2 (since 1+1=0 and X+X=0 in GF(2^128))
    poly_gf128_t* sum = poly_new(5);
    assert(poly_add(sum, p1, p2));
    assert(sum->degree == 2);
    assert(gf128_is_zero(sum->coeffs[0]));  // 1 + 1 = 0
    assert(gf128_is_zero(sum->coeffs[1]));  // 1 + 1 = 0
    assert(gf128_eq(sum->coeffs[2], gf128_one()));  // 0 + 1 = 1
    
    // Test multiplication: p1 * p2 = (1+X)(1+X+X^2) = 1 + X^3
    poly_gf128_t* prod = poly_new(5);
    assert(poly_mul(prod, p1, p2));
    assert(prod->degree == 3);
    poly_print(prod, "p1 * p2");
    
    // Test evaluation
    gf128_t x = gf128_from_le((uint8_t*)"\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    gf128_t val1 = poly_eval(p1, x);
    gf128_t expected = gf128_add(gf128_one(), x);  // 1 + x
    assert(gf128_eq(val1, expected));
    
    poly_free(p1);
    poly_free(p2);
    poly_free(sum);
    poly_free(prod);
    
    printf("Arithmetic tests passed!\n");
}

void test_polynomial_division() {
    printf("Testing polynomial division...\n");
    
    // Create dividend: X^3 + X + 1
    gf128_t dividend_coeffs[4] = { 
        gf128_one(), 
        gf128_one(), 
        gf128_zero(), 
        gf128_one() 
    };
    poly_gf128_t* dividend = poly_from_coeffs(dividend_coeffs, 4);
    
    // Create divisor: X + 1
    gf128_t divisor_coeffs[2] = { gf128_one(), gf128_one() };
    poly_gf128_t* divisor = poly_from_coeffs(divisor_coeffs, 2);
    
    poly_gf128_t* quotient = poly_new(5);
    poly_gf128_t* remainder = poly_new(5);
    
    assert(poly_div(quotient, remainder, dividend, divisor));
    
    poly_print(dividend, "dividend");
    poly_print(divisor, "divisor");
    poly_print(quotient, "quotient");
    poly_print(remainder, "remainder");
    
    // Verify: dividend = divisor * quotient + remainder
    poly_gf128_t* check = poly_new(10);
    poly_gf128_t* temp = poly_new(10);
    assert(poly_mul(temp, divisor, quotient));
    assert(poly_add(check, temp, remainder));
    
    // Check should equal dividend
    assert(check->degree == dividend->degree);
    for (size_t i = 0; i <= dividend->degree; i++) {
        assert(gf128_eq(check->coeffs[i], dividend->coeffs[i]));
    }
    
    poly_free(dividend);
    poly_free(divisor);
    poly_free(quotient);
    poly_free(remainder);
    poly_free(check);
    poly_free(temp);
    
    printf("Division tests passed!\n");
}

void test_evaluation_domain() {
    printf("Testing evaluation domain...\n");
    
    // Create a small domain of size 4
    eval_domain_t* domain = domain_new(4);
    assert(domain != NULL);
    assert(domain->size == 4);
    
    // Check that domain elements are distinct
    for (size_t i = 0; i < domain->size; i++) {
        for (size_t j = i + 1; j < domain->size; j++) {
            assert(!gf128_eq(domain->elements[i], domain->elements[j]));
        }
    }
    
    // Test vanishing polynomial
    poly_gf128_t* vanishing = compute_vanishing_polynomial(domain);
    assert(vanishing != NULL);
    assert(vanishing->degree == domain->size);
    
    // Verify vanishing polynomial vanishes on domain
    for (size_t i = 0; i < domain->size; i++) {
        gf128_t val = poly_eval(vanishing, domain->elements[i]);
        assert(gf128_is_zero(val));
    }
    
    // Test evaluation at non-domain point
    gf128_t outside = gf128_from_le((uint8_t*)"\xFF\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    gf128_t val_outside = vanishing_poly_eval(domain, outside);
    assert(!gf128_is_zero(val_outside));
    
    poly_free(vanishing);
    domain_free(domain);
    
    printf("Evaluation domain tests passed!\n");
}

int main() {
    printf("Running polynomial GF(2^128) tests...\n\n");
    
    test_polynomial_basic();
    test_polynomial_arithmetic();
    test_polynomial_division();
    test_evaluation_domain();
    
    printf("\nAll tests passed!\n");
    return 0;
}