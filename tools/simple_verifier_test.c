/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include "logger.h"

// Simplified test to check circuit format
int main() {
    // Very simple circuit:
    // - 10 input bits (8 proof + 2 public)
    // - 3 output bits (1 validity + 2 public pass-through)
    // - Just a few gates for testing
    
    FILE* out = fopen("simple_verification_test.txt", "w");
    if (!out) return 1;
    
    // Header: inputs outputs gates
    fprintf(out, "10 3 5\n");
    
    // Gates: type left right out
    // Wire 0 = constant 0
    // Wire 1 = constant 1
    // Wires 2-11 = inputs (2-9 proof, 10-11 public)
    
    // Simple "verification": AND all proof bits together
    fprintf(out, "0 2 3 12\n");    // gate 0: wire 12 = proof[0] AND proof[1]
    fprintf(out, "0 12 4 13\n");   // gate 1: wire 13 = wire12 AND proof[2]
    fprintf(out, "0 13 5 14\n");   // gate 2: wire 14 = wire13 AND proof[3]
    fprintf(out, "0 14 6 15\n");   // gate 3: wire 15 = wire14 AND proof[4]
    fprintf(out, "0 15 7 16\n");   // gate 4: wire 16 = wire15 AND proof[5] = validity bit
    
    // Outputs are: validity bit (wire 16), public[0] (wire 10), public[1] (wire 11)
    
    fclose(out);
    
    LOG_INFO("simple_verifier", "Simple verification circuit created:");
    LOG_INFO("simple_verifier", "- Inputs: 10 bits (8 proof + 2 public)");
    LOG_INFO("simple_verifier", "- Outputs: 3 bits (1 validity + 2 public)");
    LOG_INFO("simple_verifier", "- Gates: 5 (all AND gates)");
    LOG_INFO("simple_verifier", "- Circuit checks if first 6 proof bits are all 1");
    
    return 0;
}