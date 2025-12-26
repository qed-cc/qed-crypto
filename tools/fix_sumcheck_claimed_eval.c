/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/**
 * @file fix_sumcheck_claimed_eval.c
 * @brief Analysis of how to fix the sumcheck claimed evaluation issue
 * 
 * The problem: basefold_raa_prove.c doesn't compute the initial sum of the
 * witness over the hypercube. The verifier expects the first round's g(0) + g(1)
 * to equal this initial sum, but we never compute or set it!
 */

int main() {
    printf("=== SUMCHECK CLAIMED EVALUATION FIX ===\n\n");
    
    printf("PROBLEM ANALYSIS:\n");
    printf("-----------------\n");
    printf("1. The prover runs sumcheck on the witness directly\n");
    printf("2. After all rounds, it sets proof->claimed_eval = current[0]\n");
    printf("3. But the verifier expects consistency:\n");
    printf("   - First round: g(0) + g(1) should equal sum over hypercube\n");
    printf("   - Each round: g(0) + g(1) should equal previous round's evaluation\n");
    printf("   - Final: evaluation should equal proof->claimed_eval\n\n");
    
    printf("THE ISSUE:\n");
    printf("----------\n");
    printf("The prover doesn't compute the initial sum over the hypercube!\n");
    printf("The verifier starts with expected_sum = g0 + g1 from first round\n");
    printf("But this might not equal the actual sum of witness over hypercube.\n\n");
    
    printf("PROPOSED FIX:\n");
    printf("-------------\n");
    printf("Option 1: Compute initial sum and include it in proof\n");
    printf("  - Add proof->initial_sum field\n");
    printf("  - Compute sum of witness over hypercube\n");
    printf("  - Verifier checks first round matches this sum\n\n");
    
    printf("Option 2: The witness must sum to zero (constraint polynomial)\n");
    printf("  - Ensure witness encodes a constraint that sums to zero\n");
    printf("  - Set proof->claimed_eval = 0 always\n");
    printf("  - But our gate witnesses don't necessarily sum to zero!\n\n");
    
    printf("Option 3: Fix the protocol to be self-consistent\n");
    printf("  - Don't require a specific initial sum\n");
    printf("  - Just verify internal consistency of sumcheck rounds\n");
    printf("  - This is what the current code tries to do\n\n");
    
    printf("DEEPER ANALYSIS:\n");
    printf("----------------\n");
    printf("Looking at basefold_raa_verify.c line 74-76:\n");
    printf("  if (round == 0) {\n");
    printf("    expected_sum = gf128_add(g0, g1);\n");
    printf("  }\n\n");
    
    printf("This sets expected_sum from the first round's values.\n");
    printf("Then at line 119, it checks:\n");
    printf("  if (!gf128_eq(expected_sum, proof->claimed_eval))\n\n");
    
    printf("So the issue is: proof->claimed_eval is set to current[0] after\n");
    printf("all reductions, but this might not equal the first round's g0+g1!\n\n");
    
    printf("THE REAL FIX:\n");
    printf("-------------\n");
    printf("The sumcheck protocol is actually working correctly, but we're\n");
    printf("applying it to the wrong polynomial!\n\n");
    
    printf("We should be running sumcheck on the CONSTRAINT polynomial:\n");
    printf("  F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O)\n\n");
    
    printf("Not on the witness values directly!\n\n");
    
    printf("Next step: Modify the prover to:\n");
    printf("1. Compute the constraint polynomial from the witness\n");
    printf("2. Run sumcheck on the constraint polynomial\n");
    printf("3. The constraint should sum to zero over the hypercube\n");
    printf("4. Set proof->claimed_eval = 0\n");
    
    return 0;
}