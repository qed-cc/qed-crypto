/**
 * @file test_sumcheck_basic.c
 * @brief Basic tests for SumCheck protocol implementation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "gate_sumcheck.h"
#include "wiring_sumcheck.h"
#include "fold_reduce.h"
#include "wiring.h"
#include "merkle/build.h"
#include "transcript.h"
#include "gf128.h"

#define TEST_GATES 8
#define TEST_D 3  // log2(8) = 3

static void test_gate_polynomial_eval() {
    printf("Testing gate polynomial evaluation...\n");
    
    // Test XOR gate: L=1, R=0, O=1, S=0 (valid XOR)
    gf128_t L = gf128_one();
    gf128_t R = gf128_zero();
    gf128_t O = gf128_one();
    gf128_t S = gf128_zero();
    
    gf128_t result = gate_polynomial_eval(L, R, O, S);
    assert(gf128_eq(result, gf128_zero())); // Should be zero for valid gate
    
    // Test AND gate: L=1, R=1, O=1, S=1 (valid AND)
    L = gf128_one();
    R = gf128_one();
    O = gf128_one();
    S = gf128_one();
    
    result = gate_polynomial_eval(L, R, O, S);
    assert(gf128_eq(result, gf128_zero())); // Should be zero for valid gate
    
    // Test invalid gate: L=1, R=0, O=0, S=0 (invalid XOR: should be 1)
    L = gf128_one();
    R = gf128_zero();
    O = gf128_zero();
    S = gf128_zero();
    
    result = gate_polynomial_eval(L, R, O, S);
    assert(!gf128_eq(result, gf128_zero())); // Should be non-zero for invalid gate
    
    printf("✅ Gate polynomial evaluation tests passed\n");
}

static void test_wiring_polynomial_eval() {
    printf("Testing wiring polynomial evaluation...\n");
    
    // Test identity wiring: trace values = permuted values
    gf128_t trace_vals[4] = { gf128_one(), gf128_zero(), gf128_one(), gf128_zero() };
    gf128_t permuted_vals[4] = { gf128_one(), gf128_zero(), gf128_one(), gf128_zero() };
    
    gf128_t result = wiring_polynomial_eval(trace_vals, permuted_vals);
    assert(gf128_eq(result, gf128_zero())); // Should be zero for identity wiring
    
    // Test different wiring
    permuted_vals[0] = gf128_zero(); // Change L(σ(x))
    result = wiring_polynomial_eval(trace_vals, permuted_vals);
    assert(!gf128_eq(result, gf128_zero())); // Should be non-zero for different values
    
    printf("✅ Wiring polynomial evaluation tests passed\n");
}

static void test_wiring_permutation() {
    printf("Testing wiring permutation...\n");
    
    wiring_permutation_t *wiring = wiring_init(TEST_GATES);
    assert(wiring != NULL);
    
    // Add some test wiring
    assert(wiring_add_gate(wiring, 0, 2));
    assert(wiring_add_gate(wiring, 1, 3));
    assert(wiring_add_gate(wiring, 2, 4));
    assert(wiring_add_gate(wiring, 3, 5));
    
    // Pad to power of 2
    assert(wiring_pad_to_power_of_2(wiring));
    assert(wiring->is_padded);
    assert(wiring->d == TEST_D);
    
    // Test retrieval
    assert(wiring_get_destination(wiring, 0) == 2);
    assert(wiring_get_destination(wiring, 1) == 3);
    
    // Validate structure
    assert(wiring_validate(wiring));
    
    wiring_free(wiring);
    printf("✅ Wiring permutation tests passed\n");
}

static void test_fold_operations() {
    printf("Testing fold operations...\n");
    
    // Create small test codeword
    size_t test_size = 16;
    gf128_t *codeword = malloc(test_size * sizeof(gf128_t));
    assert(codeword != NULL);
    
    // Fill with test data
    for (size_t i = 0; i < test_size; i++) {
        codeword[i] = (gf128_t){0, i + 1};
    }
    
    // Test folding
    gf128_t challenge = (gf128_t){0xFEDCBA0987654321ULL, 0x1234567890ABCDEFULL};
    folded_oracle_t *folded = fold_oracle(codeword, test_size, challenge, 1);
    assert(folded != NULL);
    
    assert(folded->folded_size == test_size / 2);
    assert(folded->fold_round == 1);
    assert(gf128_eq(folded->fold_challenge, challenge));
    
    // Verify first folded value manually
    gf128_t expected = fold_compute_value(codeword[0], codeword[1], challenge);
    assert(gf128_eq(folded->folded_codeword[0], expected));
    
    fold_free_oracle(folded);
    free(codeword);
    printf("✅ Fold operations tests passed\n");
}

static void test_small_circuit() {
    printf("Testing small circuit (8 gates)...\n");
    
    // Create small test circuit trace
    size_t trace_size = TEST_GATES * 4; // 4 columns: L, R, O, S
    gf128_t *trace_codeword = malloc(trace_size * sizeof(gf128_t));
    assert(trace_codeword != NULL);
    
    // Fill with valid gate traces
    for (size_t i = 0; i < TEST_GATES; i++) {
        // Create valid XOR gates for simplicity
        trace_codeword[i * 4 + 0] = (gf128_t){0, i % 2};      // L
        trace_codeword[i * 4 + 1] = (gf128_t){0, (i + 1) % 2}; // R
        trace_codeword[i * 4 + 2] = (gf128_t){0, i % 2};      // O = L XOR R
        trace_codeword[i * 4 + 3] = gf128_zero();                   // S = 0 (XOR)
    }
    
    // Build Merkle tree
    merkle_tree_t tree;
    int result = merkle_build(trace_codeword, trace_size / MERKLE_LEAF_WORDS, &tree);
    assert(result == 0);
    
    // Test wiring permutation
    wiring_permutation_t *wiring = wiring_generate_test(TEST_GATES, 42);
    assert(wiring != NULL);
    
    // Create transcript
    fiat_shamir_t transcript;
    uint8_t seed[16] = {0};
    fs_init(&transcript, seed);
    
    // Test gate polynomial evaluation on all gates
    bool all_gates_valid = true;
    for (size_t i = 0; i < TEST_GATES; i++) {
        gf128_t L = trace_codeword[i * 4 + 0];
        gf128_t R = trace_codeword[i * 4 + 1];
        gf128_t O = trace_codeword[i * 4 + 2];
        gf128_t S = trace_codeword[i * 4 + 3];
        
        gf128_t gate_result = gate_polynomial_eval(L, R, O, S);
        if (!gf128_eq(gate_result, gf128_zero())) {
            all_gates_valid = false;
            break;
        }
    }
    assert(all_gates_valid);
    
    // Clean up
    // No need to free merkle tree - it doesn't allocate memory
    wiring_free(wiring);
    free(trace_codeword);
    
    printf("✅ Small circuit tests passed\n");
}

int main() {
    printf("=== SumCheck Basic Tests ===\n");
    
    test_gate_polynomial_eval();
    test_wiring_polynomial_eval();
    test_wiring_permutation();
    test_fold_operations();
    test_small_circuit();
    
    printf("\n🎉 All basic tests PASSED!\n");
    return 0;
}