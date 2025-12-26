#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "gf128.h"

/**
 * @brief Example application demonstrating GF128 usage
 * 
 * GF(2^128) is the Galois Field with 2^128 elements. It is used in various
 * cryptographic protocols like AES-GCM, GHASH, and other MAC algorithms.
 */
int main(int argc, char *argv[]) {
    printf("Gate Computer - GF128 Example\n");
    printf("-----------------------------\n\n");
    
    // Check if hardware acceleration is available
    printf("Hardware support:\n");
    printf("- PCLMUL support:    %s\n", gf128_has_pclmul() ? "YES" : "NO");
    printf("- AVX2 support:      %s\n", gf128_has_avx2() ? "YES" : "NO");
    printf("- AVX-512 support:   %s\n", gf128_has_avx512() ? "YES" : "NO");
#ifdef USE_GFNI
    printf("- GFNI support:      %s\n", gf128_has_gfni() ? "YES" : "NO");
#endif
    printf("\n");

    // Example values
    uint8_t bytes_a[16] = {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
        0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32, 0x10
    };
    
    uint8_t bytes_b[16] = {
        0xA0, 0xB1, 0xC2, 0xD3, 0xE4, 0xF5, 0x06, 0x17,
        0x28, 0x39, 0x4A, 0x5B, 0x6C, 0x7D, 0x8E, 0x9F
    };
    
    // Convert to GF128 elements
    gf128_t a = gf128_from_be(bytes_a);
    gf128_t b = gf128_from_be(bytes_b);
    
    // Print input values
    printf("Input values:\n");
    printf("A = 0x%016lx%016lx\n", a.hi, a.lo);
    printf("B = 0x%016lx%016lx\n", b.hi, b.lo);
    printf("\n");
    
    // Basic operations
    printf("Basic operations:\n");
    
    // Addition (XOR)
    gf128_t sum = gf128_add(a, b);
    printf("A + B = 0x%016lx%016lx\n", sum.hi, sum.lo);
    
    // Multiplication
    gf128_t product = gf128_mul(a, b);
    printf("A * B = 0x%016lx%016lx\n", product.hi, product.lo);
    
    // Check that gf128_mul() works as expected
    gf128_t product_ref = gf128_mul_base(a, b);
    if (gf128_eq(product, product_ref)) {
        printf("Verification: Hardware-accelerated multiply matches reference implementation\n");
    } else {
        printf("ERROR: Hardware-accelerated multiply does not match reference!\n");
        printf("Reference: 0x%016lx%016lx\n", product_ref.hi, product_ref.lo);
    }
    
    // Compute the multiplicative inverse of A
    gf128_t inv_a = gf128_inv(a);
    printf("A^(-1) = 0x%016lx%016lx\n", inv_a.hi, inv_a.lo);
    
    // Verify that A * A^(-1) = 1
    gf128_t verify = gf128_mul(a, inv_a);
    printf("A * A^(-1) = 0x%016lx%016lx %s\n", 
           verify.hi, verify.lo, 
           gf128_eq(verify, gf128_one()) ? "(correct)" : "(ERROR!)");
    
    // Division
    gf128_t quotient = gf128_div(product, b);
    printf("(A * B) / B = 0x%016lx%016lx %s\n", 
           quotient.hi, quotient.lo,
           gf128_eq(quotient, a) ? "(correct)" : "(ERROR!)");
    
    return 0;
}