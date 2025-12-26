/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Chess ZK Proof Circuit Generator (Fixed Version)
 * 
 * Generates actual gate circuits for chess game verification with proper dependencies.
 * Fixed: wire allocation and dependency ordering to eliminate cycles.
 */

#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

// Chess game constants
#define MAX_MOVES 100
#define BOARD_SIZE 64
#define PIECE_TYPES 6
#define ED25519_PUBKEY_SIZE 32
#define ED25519_SIGNATURE_SIZE 64
#define SHA256_DIGEST_SIZE 32

// Simplified gate counts for testing
#define GATES_PER_ED25519_VERIFY 1000  // Reduced for testing
#define GATES_PER_CHESS_MOVE 100       // Reduced for testing

typedef struct {
    uint32_t wire_id;
} wire_t;

typedef struct {
    uint8_t type;        // 0=AND, 1=XOR, 2=NOT, 3=INPUT, 4=OUTPUT
    wire_t input1;
    wire_t input2;
    wire_t output;
} gate_t;

typedef struct {
    uint32_t num_inputs;
    uint32_t num_outputs;
    uint32_t num_gates;
    uint32_t next_wire_id;
    gate_t *gates;
    uint32_t gate_count;
} circuit_t;

// Circuit builder functions
circuit_t* create_circuit(uint32_t max_gates) {
    circuit_t *circuit = malloc(sizeof(circuit_t));
    circuit->gates = malloc(sizeof(gate_t) * max_gates);
    circuit->num_gates = max_gates;
    circuit->gate_count = 0;
    circuit->next_wire_id = 3; // 0=unused, 1=constant_0, 2=constant_1
    circuit->num_inputs = 0;
    circuit->num_outputs = 0;
    return circuit;
}

wire_t allocate_wire(circuit_t *circuit) {
    wire_t wire = {circuit->next_wire_id++};
    return wire;
}

wire_t get_constant_0() {
    wire_t wire = {1};
    return wire;
}

wire_t get_constant_1() {
    wire_t wire = {2};
    return wire;
}

void add_gate(circuit_t *circuit, uint8_t type, wire_t input1, wire_t input2, wire_t output) {
    assert(circuit->gate_count < circuit->num_gates);
    gate_t *gate = &circuit->gates[circuit->gate_count++];
    gate->type = type;
    gate->input1 = input1;
    gate->input2 = input2;
    gate->output = output;
}

// Add input wires for a single chess move
wire_t* add_move_input_wires(circuit_t *circuit, uint32_t move_index) {
    // Simplified: 32 bits per move (from=8, to=8, piece=8, flags=8)
    const uint32_t bits_per_move = 32;
    wire_t *move_wires = malloc(sizeof(wire_t) * bits_per_move);
    
    for (uint32_t i = 0; i < bits_per_move; i++) {
        move_wires[i] = allocate_wire(circuit);
        circuit->num_inputs++;
    }
    
    return move_wires;
}

// Generate simplified signature verification
wire_t generate_signature_check(circuit_t *circuit, wire_t *move_bits, uint32_t num_move_bits) {
    printf("    Generating signature verification (%d gates)...\n", GATES_PER_ED25519_VERIFY);
    
    wire_t result = get_constant_1(); // Start with valid
    
    // Create a chain of XOR operations to "verify" the signature
    for (uint32_t i = 0; i < GATES_PER_ED25519_VERIFY && i < num_move_bits - 1; i++) {
        wire_t temp = allocate_wire(circuit);
        wire_t input1 = (i == 0) ? result : move_bits[i-1];
        wire_t input2 = move_bits[i];
        
        add_gate(circuit, 1, input1, input2, temp); // XOR
        result = temp;
    }
    
    return result;
}

// Generate simplified chess move validation
wire_t generate_move_validation(circuit_t *circuit, wire_t *move_bits, uint32_t num_move_bits) {
    printf("    Generating move validation (%d gates)...\n", GATES_PER_CHESS_MOVE);
    
    wire_t result = get_constant_1(); // Start with valid
    
    // Create a chain of AND operations to "validate" the move
    for (uint32_t i = 0; i < GATES_PER_CHESS_MOVE && i < num_move_bits - 1; i++) {
        wire_t temp = allocate_wire(circuit);
        wire_t input1 = (i == 0) ? result : move_bits[i % num_move_bits];
        wire_t input2 = move_bits[(i + 1) % num_move_bits];
        
        add_gate(circuit, 0, input1, input2, temp); // AND
        result = temp;
    }
    
    return result;
}

// Generate complete chess game verification circuit
void generate_chess_game_circuit(const char *output_file, uint32_t num_moves) {
    printf("🔧 Generating chess game verification circuit for %d moves\n", num_moves);
    
    // Calculate total gates needed (simplified)
    uint32_t total_gates = 0;
    total_gates += num_moves * GATES_PER_ED25519_VERIFY;  // Signature verification
    total_gates += num_moves * GATES_PER_CHESS_MOVE;      // Move validation
    total_gates += 100;                                   // Overhead and combining logic
    
    printf("  Estimated gates: %d\n", total_gates);
    printf("  Memory requirement: %.1f MB\n", total_gates * sizeof(gate_t) / 1024.0 / 1024.0);
    
    circuit_t *circuit = create_circuit(total_gates);
    
    wire_t game_valid = get_constant_1(); // Start with game being valid
    
    // Process each move sequentially
    for (uint32_t move_idx = 0; move_idx < num_moves; move_idx++) {
        printf("  Processing move %d...\n", move_idx + 1);
        
        // Add input wires for this move
        wire_t *move_wires = add_move_input_wires(circuit, move_idx);
        uint32_t num_move_bits = 32;
        
        // Verify signature for this move
        wire_t sig_valid = generate_signature_check(circuit, move_wires, num_move_bits);
        
        // Validate chess move legality
        wire_t move_valid = generate_move_validation(circuit, move_wires, num_move_bits);
        
        // Combine signature validity with move validity
        wire_t move_overall_valid = allocate_wire(circuit);
        add_gate(circuit, 0, sig_valid, move_valid, move_overall_valid); // AND
        
        // Combine with overall game validity
        wire_t new_game_valid = allocate_wire(circuit);
        add_gate(circuit, 0, game_valid, move_overall_valid, new_game_valid); // AND
        game_valid = new_game_valid;
        
        free(move_wires);
    }
    
    // Set output
    circuit->num_outputs = 1;
    
    printf("✅ Circuit generation complete!\n");
    printf("   Total gates: %d\n", circuit->gate_count);
    printf("   Input bits: %d\n", circuit->num_inputs);
    printf("   Output bits: %d\n", circuit->num_outputs);
    printf("   Final wire ID: %d\n", circuit->next_wire_id - 1);
    
    // Write circuit to file in gate_computer format
    FILE *f = fopen(output_file, "w");
    if (!f) {
        LOG_ERROR("tool", "Error: Cannot open output file %s\n", output_file);
        exit(1);
    }
    
    // Write header
    fprintf(f, "%d %d %d\n", circuit->num_inputs, circuit->gate_count, circuit->num_outputs);
    fprintf(f, "# Chess game verification circuit for %d moves (simplified)\n", num_moves);
    fprintf(f, "# Generated by chess_circuit_generator_fixed.c\n");
    
    // Write gates
    for (uint32_t i = 0; i < circuit->gate_count; i++) {
        gate_t *gate = &circuit->gates[i];
        fprintf(f, "%d %d %d %d\n", gate->type, gate->input1.wire_id, 
                gate->input2.wire_id, gate->output.wire_id);
    }
    
    // Write output wires
    fprintf(f, "%d\n", game_valid.wire_id);
    
    fclose(f);
    printf("💾 Circuit saved to %s\n", output_file);
    
    // Cleanup
    free(circuit->gates);
    free(circuit);
}

int main(int argc, char *argv[]) {
    printf("♟️  Chess Zero-Knowledge Proof Circuit Generator (Fixed)\n");
    printf("======================================================\n\n");
    
    if (argc != 3) {
        printf("Usage: %s <num_moves> <output_file>\n", argv[0]);
        printf("Example: %s 5 chess_5moves_fixed.circuit\n", argv[0]);
        return 1;
    }
    
    uint32_t num_moves = atoi(argv[1]);
    const char *output_file = argv[2];
    
    if (num_moves == 0 || num_moves > MAX_MOVES) {
        LOG_ERROR("tool", "Error: Number of moves must be 1-%d\n", MAX_MOVES);
        return 1;
    }
    
    generate_chess_game_circuit(output_file, num_moves);
    
    printf("\n🎯 Next steps:\n");
    printf("   1. Test circuit: ./build/bin/gate_computer --load-circuit %s --input $(python3 -c \"print('00' * %d)\") --dump-stats\n", output_file, num_moves * 4);
    printf("   2. Generate proof: ./build/bin/gate_computer --load-circuit %s --input [game_data] --prove chess.proof\n", output_file);
    printf("   3. Verify proof: ./build/bin/gate_computer --verify chess.proof\n");
    
    return 0;
}