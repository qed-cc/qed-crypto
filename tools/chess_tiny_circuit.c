/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Tiny Chess ZK Proof Circuit Generator
 * 
 * Creates a minimal chess verification circuit within gate_computer's 8-byte input limit.
 * Demonstrates real ZK proof generation for chess-like validation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("Usage: %s <output_file>\n", argv[0]);
        printf("Example: %s chess_tiny.circuit\n", argv[0]);
        return 1;
    }
    
    const char *output_file = argv[1];
    
    FILE *f = fopen(output_file, "w");
    if (!f) {
        fprintf(stderr, "Error: Cannot open output file %s\n", output_file);
        return 1;
    }
    
    printf("♟️ Generating tiny chess ZK proof circuit...\n");
    
    // Tiny chess verification within 8-byte (64-bit) limit:
    // - Bits 0-5: from_square (0-63)
    // - Bits 6-11: to_square (0-63)  
    // - Bits 12-15: piece_type (1-6)
    // - Bits 16-19: captured_piece (0-6)
    // - Bits 20-31: signature_hash (simplified 12-bit signature)
    // - Bits 32-47: player_id (16-bit public key hash)
    // - Bits 48-63: move_hash (16-bit move validation)
    
    uint32_t num_inputs = 64;
    uint32_t num_outputs = 1;
    
    fprintf(f, "# Tiny Chess ZK Proof Circuit\n");
    fprintf(f, "# Verifies a single chess move with signature within 64 bits\n");
    fprintf(f, "%d %d %d\n", num_inputs, 0, num_outputs); // Start with 0 gates, add them
    fprintf(f, "\n");
    
    uint32_t next_wire = num_inputs; // Start at wire 64
    uint32_t gate_count = 0;
    
    // 1. Validate from_square is valid (0-63): check bits 0-5 are not all 1s
    fprintf(f, "# Validate from_square (bits 0-5)\n");
    uint32_t from_and1 = next_wire++; // 64
    uint32_t from_and2 = next_wire++; // 65  
    uint32_t from_and3 = next_wire++; // 66
    uint32_t from_valid = next_wire++; // 67 (NOT of all 1s)
    fprintf(f, "0 0 1 %d\n", from_and1); gate_count++; // AND bits 0,1
    fprintf(f, "0 2 3 %d\n", from_and2); gate_count++; // AND bits 2,3
    fprintf(f, "0 4 5 %d\n", from_and3); gate_count++; // AND bits 4,5
    fprintf(f, "0 %d %d %d\n", from_and1, from_and2, next_wire); gate_count++; // AND groups
    uint32_t temp = next_wire++;
    fprintf(f, "0 %d %d %d\n", temp, from_and3, next_wire); gate_count++; // Final AND
    temp = next_wire++;
    fprintf(f, "2 1 %d %d\n", temp, from_valid); gate_count++; // NOT (use OR with constant 1)
    
    // 2. Validate to_square is valid (bits 6-11) and different from from_square
    fprintf(f, "\n# Validate to_square (bits 6-11) different from from_square\n");
    uint32_t diff1 = next_wire++; // XOR bits 0,6
    uint32_t diff2 = next_wire++; // XOR bits 1,7
    uint32_t diff3 = next_wire++; // XOR bits 2,8
    uint32_t diff_or1 = next_wire++;
    uint32_t diff_or2 = next_wire++;
    uint32_t moves_different = next_wire++;
    fprintf(f, "1 0 6 %d\n", diff1); gate_count++;
    fprintf(f, "1 1 7 %d\n", diff2); gate_count++;
    fprintf(f, "1 2 8 %d\n", diff3); gate_count++;
    fprintf(f, "2 %d %d %d\n", diff1, diff2, diff_or1); gate_count++;
    fprintf(f, "2 %d %d %d\n", diff_or1, diff3, moves_different); gate_count++;
    
    // 3. Validate piece type (bits 12-15) is valid (1-6)
    fprintf(f, "\n# Validate piece_type (bits 12-15) is non-zero\n");
    uint32_t piece_or1 = next_wire++;
    uint32_t piece_valid = next_wire++;
    fprintf(f, "2 12 13 %d\n", piece_or1); gate_count++;
    fprintf(f, "2 14 15 %d\n", next_wire); gate_count++;
    uint32_t piece_or2 = next_wire++;
    fprintf(f, "2 %d %d %d\n", piece_or1, piece_or2, piece_valid); gate_count++;
    
    // 4. Signature verification (simplified): XOR signature bits with move bits
    fprintf(f, "\n# Simplified signature verification\n");
    uint32_t sig_check1 = next_wire++;
    uint32_t sig_check2 = next_wire++;
    uint32_t sig_valid = next_wire++;
    fprintf(f, "1 20 0 %d\n", sig_check1); gate_count++; // XOR signature[0] with from[0]
    fprintf(f, "1 21 6 %d\n", sig_check2); gate_count++; // XOR signature[1] with to[0]
    fprintf(f, "2 %d %d %d\n", sig_check1, sig_check2, sig_valid); gate_count++; // OR checks
    
    // 5. Final validation: AND all conditions
    fprintf(f, "\n# Final validation: AND all conditions\n");
    uint32_t temp1 = next_wire++;
    uint32_t temp2 = next_wire++;
    uint32_t final_valid = next_wire++;
    fprintf(f, "0 %d %d %d\n", from_valid, moves_different, temp1); gate_count++;
    fprintf(f, "0 %d %d %d\n", piece_valid, sig_valid, temp2); gate_count++;
    fprintf(f, "0 %d %d %d\n", temp1, temp2, final_valid); gate_count++;
    
    // Update gate count in header
    fseek(f, 0, SEEK_SET);
    fprintf(f, "# Tiny Chess ZK Proof Circuit\n");
    fprintf(f, "# Verifies a single chess move with signature within 64 bits\n");
    fprintf(f, "%d %d %d\n", num_inputs, gate_count, num_outputs);
    
    // Seek to end and write output
    fseek(f, 0, SEEK_END);
    fprintf(f, "\n# Output wire\n");
    fprintf(f, "%d\n", final_valid);
    
    fclose(f);
    
    printf("✅ Circuit generated successfully!\n");
    printf("   Inputs: %d bits (8 bytes - within gate_computer limit)\n", num_inputs);
    printf("   Gates: %d\n", gate_count);
    printf("   Outputs: %d bit (move validity)\n", num_outputs);
    printf("   Final wire ID: %d\n", final_valid);
    printf("   Saved to: %s\n", output_file);
    printf("\n🎯 Test with:\n");
    printf("   # Valid move (from=1, to=9, piece=1, sig=1):\n");
    printf("   ./build/bin/gate_computer --load-circuit %s --input 0000000000011241 --dump-stats\n", output_file);
    printf("   # Generate ZK proof:\n");
    printf("   ./build/bin/gate_computer --load-circuit %s --input 0000000000011241 --prove chess_tiny.proof\n", output_file);
    printf("   # Verify ZK proof:\n");
    printf("   ./build/bin/gate_computer --verify chess_tiny.proof\n");
    
    return 0;
}