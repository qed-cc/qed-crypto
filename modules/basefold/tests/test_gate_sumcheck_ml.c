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

// Test with a tiny 2-variable (4 gate) circuit
static void test_tiny_circuit(void) {
    printf("Testing 2-variable circuit (4 gates)...\n");
    
    // Create multilinear polynomials for a simple circuit
    // Gate 0: XOR(0,1) = 1
    // Gate 1: AND(1,1) = 1  
    // Gate 2: XOR(1,0) = 1
    // Gate 3: AND(0,0) = 0
    
    multilinear_poly_t* L = multilinear_create(2);
    multilinear_poly_t* R = multilinear_create(2);
    multilinear_poly_t* O = multilinear_create(2);
    multilinear_poly_t* S = multilinear_create(2);
    
    // Set evaluations
    // L values: [0, 1, 1, 0]
    L->evaluations[0] = gf128_zero();
    L->evaluations[1] = gf128_one();
    L->evaluations[2] = gf128_one();
    L->evaluations[3] = gf128_zero();
    
    // R values: [1, 1, 0, 0]
    R->evaluations[0] = gf128_one();
    R->evaluations[1] = gf128_one();
    R->evaluations[2] = gf128_zero();
    R->evaluations[3] = gf128_zero();
    
    // O values: [1, 1, 1, 0]
    O->evaluations[0] = gf128_one();
    O->evaluations[1] = gf128_one();
    O->evaluations[2] = gf128_one();
    O->evaluations[3] = gf128_zero();
    
    // S values: [0, 1, 0, 1] (0=XOR, 1=AND)
    S->evaluations[0] = gf128_zero();
    S->evaluations[1] = gf128_one();
    S->evaluations[2] = gf128_zero();
    S->evaluations[3] = gf128_one();
    
    // Create instance
    gate_sumcheck_instance_t instance = {
        .L = L,
        .R = R,
        .O = O,
        .S = S,
        .num_vars = 2
    };
    
    // Verify constraints are satisfied
    printf("  Checking gate constraints...\n");
    for (size_t i = 0; i < 4; i++) {
        gf128_t point[2];
        multilinear_index_to_vec(i, point, 2);
        gf128_t f_val = gate_constraint_ml_eval(&instance, point);
        
        printf("    Gate %zu: F = %016lx%016lx %s\n", i, 
               f_val.hi, f_val.lo,
               gf128_is_zero(f_val) ? "(valid)" : "(INVALID!)");
        
        assert(gf128_is_zero(f_val));
    }
    
    // Create transcript
    fiat_shamir_t transcript;
    uint8_t seed[16] = {0};  // Zero seed for testing
    fs_init(&transcript, seed);
    
    // Generate proof
    printf("  Generating SumCheck proof...\n");
    gf128_t claimed_sum = gf128_zero();  // Sum should be 0 for valid gates
    gate_sumcheck_proof_t* proof = gate_sumcheck_ml_prove(&instance, &transcript, claimed_sum);
    assert(proof != NULL);
    printf("  Generated proof with %zu rounds\n", proof->num_rounds);
    assert(proof->num_rounds == 2);
    
    // Print round polynomials
    for (size_t i = 0; i < proof->num_rounds; i++) {
        printf("    Round %zu polynomial (degree %zu): ", i, proof->round_polys[i].degree);
        for (size_t j = 0; j <= proof->round_polys[i].degree && j < 4; j++) {
            printf("%016lx ", proof->round_polys[i].coeffs[j].lo);
        }
        printf("\n");
        
        // Check g(0) + g(1)
        gf128_t g0 = proof->round_polys[i].coeffs[0];
        gf128_t g1 = gf128_add(proof->round_polys[i].coeffs[0], proof->round_polys[i].coeffs[1]);
        if (proof->round_polys[i].degree >= 2) {
            g1 = gf128_add(g1, proof->round_polys[i].coeffs[2]);
        }
        gf128_t sum = gf128_add(g0, g1);
        printf("      g(0)=%016lx, g(1)=%016lx, sum=%016lx\n", g0.lo, g1.lo, sum.lo);
    }
    
    // Verify proof
    printf("  Verifying SumCheck proof...\n");
    fs_init(&transcript, seed);  // Reset transcript with same seed
    bool valid = gate_sumcheck_ml_verify(proof, &transcript, claimed_sum, 2);
    assert(valid);
    printf("  ✓ Proof verified successfully!\n");
    
    // Cleanup
    gate_sumcheck_proof_free(proof);
    multilinear_free(L);
    multilinear_free(R);
    multilinear_free(O);
    multilinear_free(S);
}

// Test with invalid gates (should fail)
static void test_invalid_gates(void) {
    printf("Testing invalid gates...\n");
    
    multilinear_poly_t* L = multilinear_create(1);
    multilinear_poly_t* R = multilinear_create(1);
    multilinear_poly_t* O = multilinear_create(1);
    multilinear_poly_t* S = multilinear_create(1);
    
    // Create an invalid AND gate: 1 AND 1 = 0 (should be 1)
    L->evaluations[0] = gf128_one();
    R->evaluations[0] = gf128_one();
    O->evaluations[0] = gf128_zero();  // Wrong output!
    S->evaluations[0] = gf128_one();   // AND gate
    
    // Valid XOR gate: 0 XOR 1 = 1
    L->evaluations[1] = gf128_zero();
    R->evaluations[1] = gf128_one();
    O->evaluations[1] = gf128_one();
    S->evaluations[1] = gf128_zero();  // XOR gate
    
    gate_sumcheck_instance_t instance = {
        .L = L, .R = R, .O = O, .S = S, .num_vars = 1
    };
    
    // Check constraints
    gf128_t sum = gf128_zero();
    for (size_t i = 0; i < 2; i++) {
        gf128_t point[1] = {i ? gf128_one() : gf128_zero()};
        gf128_t f_val = gate_constraint_ml_eval(&instance, point);
        sum = gf128_add(sum, f_val);
        printf("  Gate %zu: F = %016lx%016lx\n", i, f_val.hi, f_val.lo);
    }
    
    printf("  Total sum: %016lx%016lx (should be non-zero)\n", sum.hi, sum.lo);
    assert(!gf128_is_zero(sum));
    
    // Try to prove with wrong claimed sum (should fail verification)
    fiat_shamir_t transcript;
    uint8_t seed[16] = {0};
    fs_init(&transcript, seed);
    
    gate_sumcheck_proof_t* proof = gate_sumcheck_ml_prove(&instance, &transcript, gf128_zero());
    
    fs_init(&transcript, seed);
    bool valid = gate_sumcheck_ml_verify(proof, &transcript, gf128_zero(), 1);
    assert(!valid);
    printf("  ✓ Invalid proof correctly rejected!\n");
    
    // Cleanup
    gate_sumcheck_proof_free(proof);
    multilinear_free(L);
    multilinear_free(R);
    multilinear_free(O);
    multilinear_free(S);
}

// Test edge cases
static void test_edge_cases(void) {
    printf("Testing edge cases...\n");
    
    // Test with 0 variables (single gate)
    multilinear_poly_t* L = multilinear_create(0);
    multilinear_poly_t* R = multilinear_create(0);
    multilinear_poly_t* O = multilinear_create(0);
    multilinear_poly_t* S = multilinear_create(0);
    
    // Single XOR gate: 1 XOR 1 = 0
    L->evaluations[0] = gf128_one();
    R->evaluations[0] = gf128_one();
    O->evaluations[0] = gf128_zero();
    S->evaluations[0] = gf128_zero();
    
    gate_sumcheck_instance_t instance = {
        .L = L, .R = R, .O = O, .S = S, .num_vars = 0
    };
    
    // With 0 variables, the "sum" is just the single evaluation
    gf128_t dummy[1];
    gf128_t f_val = gate_constraint_ml_eval(&instance, dummy);
    assert(gf128_is_zero(f_val));
    
    printf("  ✓ 0-variable case handled correctly\n");
    
    multilinear_free(L);
    multilinear_free(R);
    multilinear_free(O);
    multilinear_free(S);
}

// Test performance with larger circuit
static void test_performance(void) {
    printf("Testing performance with larger circuits...\n");
    
    for (size_t num_vars = 4; num_vars <= 12; num_vars += 2) {
        size_t num_gates = 1ULL << num_vars;
        
        // Create random valid circuit
        multilinear_poly_t* L = multilinear_create(num_vars);
        multilinear_poly_t* R = multilinear_create(num_vars);
        multilinear_poly_t* O = multilinear_create(num_vars);
        multilinear_poly_t* S = multilinear_create(num_vars);
        
        // Fill with valid gates
        for (size_t i = 0; i < num_gates; i++) {
            // Random inputs
            L->evaluations[i] = (i & 1) ? gf128_one() : gf128_zero();
            R->evaluations[i] = (i & 2) ? gf128_one() : gf128_zero();
            S->evaluations[i] = (i & 4) ? gf128_one() : gf128_zero();
            
            // Compute correct output
            if (gf128_is_zero(S->evaluations[i])) {
                // XOR gate
                O->evaluations[i] = gf128_add(L->evaluations[i], R->evaluations[i]);
            } else {
                // AND gate
                O->evaluations[i] = gf128_mul(L->evaluations[i], R->evaluations[i]);
            }
        }
        
        gate_sumcheck_instance_t instance = {
            .L = L, .R = R, .O = O, .S = S, .num_vars = num_vars
        };
        
        // Time proof generation
        fiat_shamir_t transcript;
        uint8_t seed[16] = {0};
        fs_init(&transcript, seed);
        
        gate_sumcheck_proof_t* proof = gate_sumcheck_ml_prove(&instance, &transcript, gf128_zero());
        assert(proof != NULL);
        
        printf("  %zu variables (%zu gates): Generated %zu round proof\n",
               num_vars, num_gates, proof->num_rounds);
        
        // Verify
        fs_init(&transcript, seed);
        bool valid = gate_sumcheck_ml_verify(proof, &transcript, gf128_zero(), num_vars);
        assert(valid);
        
        // Cleanup
        gate_sumcheck_proof_free(proof);
        multilinear_free(L);
        multilinear_free(R);
        multilinear_free(O);
        multilinear_free(S);
    }
    
    printf("  ✓ Performance test passed\n");
}

int main(void) {
    printf("=== Multilinear Gate SumCheck Tests ===\n\n");
    
    test_tiny_circuit();
    test_invalid_gates();
    test_edge_cases();
    test_performance();
    
    printf("\n✅ All multilinear gate SumCheck tests passed!\n");
    return 0;
}