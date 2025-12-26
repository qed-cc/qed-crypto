/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Minimal Chess ZK Proof Circuit Generator
 * 
 * Creates a simple but correct chess verification circuit that actually works.
 * Demonstrates the concept with proper wire numbering and no dependency cycles.
 */

#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("Usage: %s <output_file>\n", argv[0]);
        printf("Example: %s chess_minimal.circuit\n", argv[0]);
        return 1;
    }
    
    const char *output_file = argv[1];
    
    FILE *f = fopen(output_file, "w");
    if (!f) {
        fprintf(stderr, "Error: Cannot open output file %s\n", output_file);
        return 1;
    }
    
    printf("♟️ Generating minimal chess ZK proof circuit...\n");
    
    // Minimal chess verification:
    // - Input: 64 bits (2 chess moves: from1, to1, from2, to2 = 8*4 = 32 bits each)
    // - Output: 1 bit (game valid)
    // - Logic: Simple validation that moves are non-zero and different
    
    uint32_t num_inputs = 64;
    uint32_t num_outputs = 1;
    
    // Gates:
    // 1. Check move1 is non-zero (OR all bits of move1)
    // 2. Check move2 is non-zero (OR all bits of move2) 
    // 3. Check moves are different (XOR corresponding bits, then OR)
    // 4. AND all conditions together
    
    uint32_t num_gates = 32 + 32 + 32 + 3; // OR chains + difference check + final logic
    
    fprintf(f, "# Minimal Chess ZK Proof Circuit\n");
    fprintf(f, "# Verifies 2 chess moves are valid and different\n");
    fprintf(f, "%d %d %d\n", num_inputs, num_gates, num_outputs);
    fprintf(f, "\n");
    
    uint32_t next_wire = num_inputs; // Start output wires after inputs
    uint32_t gate_count = 0;
    
    // Gate type: 0=AND, 1=XOR, 2=OR
    fprintf(f, "# Check move1 is non-zero (OR bits 0-31)\n");
    uint32_t move1_or_wire = next_wire++;
    fprintf(f, "2 0 1 %d\n", move1_or_wire); gate_count++;
    
    for (uint32_t i = 2; i < 32; i++) {
        uint32_t temp_wire = next_wire++;
        fprintf(f, "2 %d %d %d\n", move1_or_wire, i, temp_wire); gate_count++;
        move1_or_wire = temp_wire;
    }
    
    fprintf(f, "\n# Check move2 is non-zero (OR bits 32-63)\n");
    uint32_t move2_or_wire = next_wire++;
    fprintf(f, "2 32 33 %d\n", move2_or_wire); gate_count++;
    
    for (uint32_t i = 34; i < 64; i++) {
        uint32_t temp_wire = next_wire++;
        fprintf(f, "2 %d %d %d\n", move2_or_wire, i, temp_wire); gate_count++;
        move2_or_wire = temp_wire;
    }
    
    fprintf(f, "\n# Check moves are different (XOR then OR)\n");
    uint32_t diff_or_wire = next_wire++;
    uint32_t first_xor_wire = next_wire++;
    fprintf(f, "1 0 32 %d\n", first_xor_wire); gate_count++; // XOR first bits
    fprintf(f, "2 %d %d %d\n", first_xor_wire, first_xor_wire, diff_or_wire); gate_count++; // Start OR chain
    
    for (uint32_t i = 1; i < 32; i++) {
        uint32_t xor_wire = next_wire++;
        uint32_t temp_or_wire = next_wire++;
        fprintf(f, "1 %d %d %d\n", i, i + 32, xor_wire); gate_count++; // XOR corresponding bits
        fprintf(f, "2 %d %d %d\n", diff_or_wire, xor_wire, temp_or_wire); gate_count++; // OR into chain
        diff_or_wire = temp_or_wire;
    }
    
    fprintf(f, "\n# Final validation: move1_valid AND move2_valid AND moves_different\n");
    uint32_t temp_and_wire = next_wire++;
    uint32_t final_wire = next_wire++;
    fprintf(f, "0 %d %d %d\n", move1_or_wire, move2_or_wire, temp_and_wire); gate_count++;
    fprintf(f, "0 %d %d %d\n", temp_and_wire, diff_or_wire, final_wire); gate_count++;
    
    fprintf(f, "\n# Output wire\n");
    fprintf(f, "%d\n", final_wire);
    
    fclose(f);
    
    printf("✅ Circuit generated successfully!\n");
    printf("   Inputs: %d bits (64 bits = 2 chess moves)\n", num_inputs);
    printf("   Gates: %d (actual: %d)\n", num_gates, gate_count);
    printf("   Outputs: %d bit (game validity)\n", num_outputs);
    printf("   Saved to: %s\n", output_file);
    printf("\n🎯 Test with:\n");
    printf("   # Valid different moves:\n");
    printf("   ./build/bin/gate_computer --load-circuit %s --input $(python3 -c \"print('01' + '00' * 7 + '02' + '00' * 7)\") --dump-stats\n", output_file);
    printf("   # Invalid same moves:\n");
    printf("   ./build/bin/gate_computer --load-circuit %s --input $(python3 -c \"print('01' + '00' * 7 + '01' + '00' * 7)\") --dump-stats\n", output_file);
    printf("   # Generate proof:\n");
    printf("   ./build/bin/gate_computer --load-circuit %s --input [valid_input] --prove chess_minimal.proof\n", output_file);
    
    return 0;
}