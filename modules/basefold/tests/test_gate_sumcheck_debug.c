#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "gate_sumcheck_multilinear.h"
#include "transcript.h"
#include "sha3.h"

// Helper to create gf128 from int
static inline gf128_t gf128_from_int(int x) {
    gf128_t result = {0, (uint64_t)x};
    return result;
}

// Debug tiny circuit
static void debug_tiny_circuit(void) {
    printf("=== Debug Tiny Circuit ===\n\n");
    
    // Create a single AND gate: 1 AND 1 = 1
    multilinear_poly_t* L = multilinear_create(0);  // 0 vars = 1 gate
    multilinear_poly_t* R = multilinear_create(0);
    multilinear_poly_t* O = multilinear_create(0);
    multilinear_poly_t* S = multilinear_create(0);
    
    L->evaluations[0] = gf128_one();
    R->evaluations[0] = gf128_one();
    O->evaluations[0] = gf128_one();
    S->evaluations[0] = gf128_one();  // AND gate
    
    gate_sumcheck_instance_t instance = {
        .L = L, .R = R, .O = O, .S = S, .num_vars = 0
    };
    
    // Check constraint
    gf128_t dummy[1];
    gf128_t f_val = gate_constraint_ml_eval(&instance, dummy);
    printf("Single AND gate constraint: F = %016lx%016lx (should be 0)\n", 
           f_val.hi, f_val.lo);
    assert(gf128_is_zero(f_val));
    
    // With 0 variables, there are no rounds
    fiat_shamir_t transcript;
    uint8_t seed[16] = {0};
    fs_init(&transcript, seed);
    
    gate_sumcheck_proof_t* proof = gate_sumcheck_ml_prove(&instance, &transcript, gf128_zero());
    assert(proof != NULL);
    assert(proof->num_rounds == 0);
    
    printf("✓ 0-variable case works\n\n");
    
    // Now test 1 variable (2 gates)
    printf("=== Debug 1-Variable Circuit ===\n\n");
    
    multilinear_free(L);
    multilinear_free(R);
    multilinear_free(O);
    multilinear_free(S);
    gate_sumcheck_proof_free(proof);
    
    L = multilinear_create(1);
    R = multilinear_create(1);
    O = multilinear_create(1);
    S = multilinear_create(1);
    
    // Gate 0: 0 XOR 1 = 1
    L->evaluations[0] = gf128_zero();
    R->evaluations[0] = gf128_one();
    O->evaluations[0] = gf128_one();
    S->evaluations[0] = gf128_zero();
    
    // Gate 1: 1 AND 1 = 1
    L->evaluations[1] = gf128_one();
    R->evaluations[1] = gf128_one();
    O->evaluations[1] = gf128_one();
    S->evaluations[1] = gf128_one();
    
    instance.L = L;
    instance.R = R;
    instance.O = O;
    instance.S = S;
    instance.num_vars = 1;
    
    // Check constraints
    printf("Checking gate constraints:\n");
    gf128_t sum = gf128_zero();
    for (int i = 0; i < 2; i++) {
        gf128_t point[1] = {i ? gf128_one() : gf128_zero()};
        gf128_t f_val = gate_constraint_ml_eval(&instance, point);
        printf("  Gate %d: F = %016lx%016lx\n", i, f_val.hi, f_val.lo);
        sum = gf128_add(sum, f_val);
    }
    printf("Total sum: %016lx%016lx (should be 0)\n\n", sum.hi, sum.lo);
    assert(gf128_is_zero(sum));
    
    // Debug round polynomial computation
    printf("Computing round polynomial manually:\n");
    round_polynomial_t round_poly;
    compute_round_polynomial_ml(&instance, 0, NULL, &round_poly);
    
    printf("Round polynomial coefficients:\n");
    for (int i = 0; i <= 3; i++) {
        printf("  g[%d] = %016lx%016lx\n", i, 
               round_poly.coeffs[i].hi, round_poly.coeffs[i].lo);
    }
    
    // Check g(0) + g(1)
    gf128_t g0 = round_poly.coeffs[0];
    gf128_t g1 = gf128_add(round_poly.coeffs[0], round_poly.coeffs[1]);
    if (round_poly.degree >= 2) {
        g1 = gf128_add(g1, round_poly.coeffs[2]);
    }
    if (round_poly.degree >= 3) {
        g1 = gf128_add(g1, round_poly.coeffs[3]);
    }
    
    gf128_t g_sum = gf128_add(g0, g1);
    printf("\ng(0) = %016lx%016lx\n", g0.hi, g0.lo);
    printf("g(1) = %016lx%016lx\n", g1.hi, g1.lo);
    printf("g(0) + g(1) = %016lx%016lx (should be 0)\n", g_sum.hi, g_sum.lo);
    
    multilinear_free(L);
    multilinear_free(R);
    multilinear_free(O);
    multilinear_free(S);
}

int main(void) {
    debug_tiny_circuit();
    return 0;
}