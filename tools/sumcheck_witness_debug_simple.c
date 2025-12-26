/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/**
 * @file sumcheck_witness_debug_simple.c
 * @brief Simplified debug tool to understand sumcheck witness structure
 */

// GF128 type
typedef struct {
    uint64_t hi;
    uint64_t lo;
} gf128_t;

// Simple GF128 operations
static inline gf128_t gf128_zero(void) { return (gf128_t){0, 0}; }
static inline gf128_t gf128_one(void)  { return (gf128_t){0, 1}; }
static inline gf128_t gf128_add(gf128_t a, gf128_t b) {
    return (gf128_t){a.hi ^ b.hi, a.lo ^ b.lo};
}
static inline int gf128_is_zero(gf128_t a) {
    return (a.hi == 0) && (a.lo == 0);
}

// Calculate sum of witness over boolean hypercube
gf128_t calculate_hypercube_sum(const gf128_t *witness, size_t num_vars) {
    size_t size = 1ULL << num_vars;
    gf128_t sum = gf128_zero();
    
    for (size_t i = 0; i < size; i++) {
        sum = gf128_add(sum, witness[i]);
    }
    
    return sum;
}

// Print witness structure for gate constraints
void analyze_gate_witness(size_t num_vars) {
    size_t size = 1ULL << num_vars;
    size_t num_rows = size / 4;
    
    printf("\nAnalyzing witness for %zu variables:\n", num_vars);
    printf("=====================================\n");
    printf("  Total witness size: %zu elements\n", size);
    printf("  Number of gates: %zu\n", num_rows);
    printf("  Columns: L (left), R (right), O (output), S (selector)\n");
    
    // Create a simple witness with all zeros except one gate
    gf128_t *witness = calloc(size, sizeof(gf128_t));
    
    // Set up one XOR gate: 1 XOR 1 = 0
    // Gate 0: L=1, R=1, O=0, S=0 (XOR gate)
    witness[0] = gf128_one();           // L
    witness[num_rows] = gf128_one();    // R
    witness[2 * num_rows] = gf128_zero(); // O
    witness[3 * num_rows] = gf128_zero(); // S
    
    // Calculate sum over hypercube
    gf128_t sum = calculate_hypercube_sum(witness, num_vars);
    
    printf("\n  Sum over hypercube: ");
    if (gf128_is_zero(sum)) {
        printf("0 (ZERO)\n");
    } else {
        printf("NON-ZERO (hi=%016llx, lo=%016llx)\n", 
               (unsigned long long)sum.hi, 
               (unsigned long long)sum.lo);
    }
    
    printf("\n  Observation: Witness with gate values doesn't sum to zero!\n");
    printf("  The CONSTRAINT polynomial should sum to zero, not the witness.\n");
    
    free(witness);
}

// Analyze what happens with different witness patterns
void analyze_witness_patterns() {
    printf("\n=== WITNESS PATTERN ANALYSIS ===\n");
    
    // Pattern 1: Empty witness
    printf("\nPattern 1: Empty witness (all zeros)\n");
    size_t num_vars = 10;
    size_t size = 1ULL << num_vars;
    gf128_t *witness = calloc(size, sizeof(gf128_t));
    gf128_t sum = calculate_hypercube_sum(witness, num_vars);
    printf("  Sum: %s\n", gf128_is_zero(sum) ? "ZERO" : "NON-ZERO");
    free(witness);
    
    // Pattern 2: Single one
    printf("\nPattern 2: Single one at position 0\n");
    witness = calloc(size, sizeof(gf128_t));
    witness[0] = gf128_one();
    sum = calculate_hypercube_sum(witness, num_vars);
    printf("  Sum: %s\n", gf128_is_zero(sum) ? "ZERO" : "NON-ZERO");
    free(witness);
    
    // Pattern 3: Even number of ones
    printf("\nPattern 3: Two ones (positions 0 and 1)\n");
    witness = calloc(size, sizeof(gf128_t));
    witness[0] = gf128_one();
    witness[1] = gf128_one();
    sum = calculate_hypercube_sum(witness, num_vars);
    printf("  Sum: %s (XOR of two 1s = 0)\n", gf128_is_zero(sum) ? "ZERO" : "NON-ZERO");
    free(witness);
}

int main() {
    printf("=== SUMCHECK WITNESS DEBUG (SIMPLIFIED) ===\n");
    printf("Understanding witness structure for gate constraints\n");
    
    // Analyze different witness sizes
    size_t sizes[] = {8, 10, 12, 14};
    for (int i = 0; i < 4; i++) {
        analyze_gate_witness(sizes[i]);
    }
    
    // Analyze witness patterns
    analyze_witness_patterns();
    
    printf("\n=== KEY INSIGHTS ===\n");
    printf("1. Witness encodes gate evaluations in 4 columns (L,R,O,S)\n");
    printf("2. The witness itself doesn't need to sum to zero\n");
    printf("3. The CONSTRAINT F(L,R,O,S) should sum to zero\n");
    printf("4. Sumcheck verifies the claimed sum matches actual sum\n");
    printf("5. We need to set proof->claimed_eval correctly!\n");
    
    return 0;
}