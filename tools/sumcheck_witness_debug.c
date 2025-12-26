/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../modules/basefold_raa/include/gate_witness_generator.h"
#include "../modules/gf128/include/gf128.h"

/**
 * @file sumcheck_witness_debug.c
 * @brief Debug tool to understand what sumcheck expects from witnesses
 */

// Calculate sum of polynomial over boolean hypercube
gf128_t calculate_hypercube_sum(const gf128_t *witness, size_t num_vars) {
    size_t size = 1ULL << num_vars;
    gf128_t sum = gf128_zero();
    
    for (size_t i = 0; i < size; i++) {
        sum = gf128_add(sum, witness[i]);
    }
    
    return sum;
}

// Print witness structure
void print_witness_structure(const gf128_t *witness, size_t num_vars) {
    size_t size = 1ULL << num_vars;
    size_t num_rows = size / 4;
    
    printf("Witness structure (4 columns):\n");
    printf("  Total size: %zu elements\n", size);
    printf("  Rows: %zu\n", num_rows);
    printf("  Columns: L, R, O, S\n\n");
    
    // Show first few rows
    printf("First 5 rows:\n");
    printf("Row | L | R | O | S | Constraint\n");
    printf("----|---|---|---|---|------------\n");
    
    for (size_t i = 0; i < 5 && i < num_rows; i++) {
        gf128_t L = witness[i];
        gf128_t R = witness[num_rows + i];
        gf128_t O = witness[2 * num_rows + i];
        gf128_t S = witness[3 * num_rows + i];
        
        // Calculate constraint: S*(L*R - O) + (1-S)*(L + R - O)
        // In GF(2^128), subtraction is the same as addition (XOR)
        gf128_t mul_gate = gf128_add(gf128_mul(L, R), O);
        gf128_t add_gate = gf128_add(gf128_add(L, R), O);
        gf128_t one_minus_s = gf128_add(gf128_one(), S);
        gf128_t constraint = gf128_add(
            gf128_mul(S, mul_gate),
            gf128_mul(one_minus_s, add_gate)
        );
        
        printf("%3zu | %d | %d | %d | %d | ", i,
               (int)(L.lo & 1),
               (int)(R.lo & 1), 
               (int)(O.lo & 1),
               (int)(S.lo & 1));
               
        if (gf128_is_zero(constraint)) {
            printf("0 ✓\n");
        } else {
            printf("%016llx%016llx ✗\n", 
                   (unsigned long long)constraint.hi,
                   (unsigned long long)constraint.lo);
        }
    }
}

int main() {
    printf("=== SUMCHECK WITNESS DEBUG TOOL ===\n\n");
    
    // Test different witness sizes
    size_t test_sizes[] = {8, 10, 12, 14};
    
    for (int t = 0; t < 4; t++) {
        size_t num_vars = test_sizes[t];
        printf("Testing with %zu variables (witness size %zu):\n", 
               num_vars, 1ULL << num_vars);
        printf("================================================\n");
        
        // Generate simple XOR witness
        gf128_t *witness = generate_simple_xor_witness(num_vars);
        if (!witness) {
            printf("Failed to generate witness\n");
            continue;
        }
        
        // Print structure
        print_witness_structure(witness, num_vars);
        
        // Calculate sum over hypercube
        gf128_t sum = calculate_hypercube_sum(witness, num_vars);
        printf("\nSum over hypercube: ");
        if (gf128_is_zero(sum)) {
            printf("0 (ZERO)\n");
        } else {
            uint8_t sum_bytes[16];
            gf128_to_bytes(sum, sum_bytes);
            printf("0x");
            for (int i = 0; i < 16; i++) {
                printf("%02x", sum_bytes[i]);
            }
            printf("\n");
        }
        
        // Check if witness satisfies constraints
        int valid = verify_gate_constraints(witness, 1ULL << num_vars);
        printf("Gate constraints: %s\n", valid == 0 ? "VALID ✓" : "INVALID ✗");
        
        // Try with multi-gate witness
        printf("\nMulti-gate witness:\n");
        free(witness);
        witness = generate_multi_gate_witness(num_vars);
        if (witness) {
            sum = calculate_hypercube_sum(witness, num_vars);
            printf("  Sum over hypercube: ");
            if (gf128_is_zero(sum)) {
                printf("0 (ZERO)\n");
            } else {
                printf("NON-ZERO\n");
            }
            valid = verify_gate_constraints(witness, 1ULL << num_vars);
            printf("  Gate constraints: %s\n", valid == 0 ? "VALID ✓" : "INVALID ✗");
        }
        
        free(witness);
        printf("\n");
    }
    
    // Understanding sumcheck protocol
    printf("\nSUMCHECK PROTOCOL UNDERSTANDING:\n");
    printf("================================\n");
    printf("1. The prover claims: sum of f over hypercube = claimed_eval\n");
    printf("2. Verifier checks this interactively via sumcheck rounds\n");
    printf("3. Our witnesses are polynomials encoding gate constraints\n");
    printf("4. The constraint polynomial should sum to ZERO over hypercube\n");
    printf("5. But the witness itself might not sum to zero!\n\n");
    
    printf("KEY INSIGHT: The witness encodes gate values (L,R,O,S)\n");
    printf("The CONSTRAINT F(L,R,O,S) sums to zero, not the witness!\n\n");
    
    printf("Next step: Modify basefold_raa_prove to:\n");
    printf("1. Calculate actual sum of witness over hypercube\n");
    printf("2. Set proof->claimed_eval to this sum\n");
    printf("3. Run sumcheck protocol with correct claim\n");
    
    return 0;
}