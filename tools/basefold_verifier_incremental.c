/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file basefold_verifier_incremental.c
 * @brief Incremental BaseFold verification circuit builder
 * 
 * Builds the verification circuit piece by piece to track gate counts
 */

#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

// Circuit parameters
#define GF128_BITS 128
#define SHA3_256_BITS 256
#define PUBLIC_INPUT_BITS 256
#define PROOF_SIZE_BITS 7910755

typedef struct {
    FILE* file;
    uint32_t num_gates;
    uint32_t next_wire;
    uint32_t zero_wire;
    uint32_t one_wire;
} circuit_t;

static circuit_t* circuit_create(const char* filename) {
    circuit_t* c = calloc(1, sizeof(circuit_t));
    c->file = fopen(filename, "w");
    if (!c->file) {
        free(c);
        return NULL;
    }
    
    // Reserve space for header (will write at end)
    fprintf(c->file, "                                        \n");
    
    c->zero_wire = 0;
    c->one_wire = 1;
    c->next_wire = 2;  // Start after constants
    
    return c;
}

static uint32_t wire_new(circuit_t* c) {
    return c->next_wire++;
}

static void gate_and(circuit_t* c, uint32_t a, uint32_t b, uint32_t out) {
    fprintf(c->file, "0 %u %u %u\n", a, b, out);
    c->num_gates++;
}

static void gate_xor(circuit_t* c, uint32_t a, uint32_t b, uint32_t out) {
    fprintf(c->file, "1 %u %u %u\n", a, b, out);
    c->num_gates++;
}

static uint32_t gate_not(circuit_t* c, uint32_t a) {
    uint32_t out = wire_new(c);
    gate_xor(c, a, c->one_wire, out);
    return out;
}

// Add GF128 field addition (128 XOR gates)
static void add_gf128_add(circuit_t* c, uint32_t* a, uint32_t* b, uint32_t* out) {
    for (int i = 0; i < GF128_BITS; i++) {
        out[i] = wire_new(c);
        gate_xor(c, a[i], b[i], out[i]);
    }
}

// Add simplified GF128 multiplication (placeholder)
static void add_gf128_mul(circuit_t* c, uint32_t* a, uint32_t* b, uint32_t* out) {
    // Real implementation would be ~20,000 gates
    // For now, just XOR to have something
    for (int i = 0; i < GF128_BITS; i++) {
        out[i] = wire_new(c);
        gate_xor(c, a[i], b[i], out[i]);
    }
}

// Add SHA3-256 circuit (placeholder)
static uint32_t add_sha3_256(circuit_t* c, uint32_t* input, size_t input_bits) {
    // Real SHA3 would be ~18,000 gates
    // For now, just return XOR of first few bits
    uint32_t result = input[0];
    for (size_t i = 1; i < 8 && i < input_bits; i++) {
        uint32_t temp = wire_new(c);
        gate_xor(c, result, input[i], temp);
        result = temp;
    }
    return result;
}

// Add equality check for GF128 elements
static uint32_t add_gf128_equal(circuit_t* c, uint32_t* a, uint32_t* b) {
    uint32_t equal = c->one_wire;
    
    for (int i = 0; i < GF128_BITS; i++) {
        uint32_t bit_diff = wire_new(c);
        gate_xor(c, a[i], b[i], bit_diff);
        
        uint32_t bit_equal = gate_not(c, bit_diff);
        
        uint32_t new_equal = wire_new(c);
        gate_and(c, equal, bit_equal, new_equal);
        equal = new_equal;
    }
    
    return equal;
}

// Main circuit builder
static void build_verification_circuit(circuit_t* c) {
    printf("Building BaseFold verification circuit incrementally...\n\n");
    
    // Allocate input wires
    uint32_t num_inputs = PROOF_SIZE_BITS + PUBLIC_INPUT_BITS;
    uint32_t* proof_wires = malloc(PROOF_SIZE_BITS * sizeof(uint32_t));
    uint32_t* public_wires = malloc(PUBLIC_INPUT_BITS * sizeof(uint32_t));
    
    // Inputs start at wire 2 (after constants)
    for (uint32_t i = 0; i < PROOF_SIZE_BITS; i++) {
        proof_wires[i] = c->next_wire++;
    }
    for (uint32_t i = 0; i < PUBLIC_INPUT_BITS; i++) {
        public_wires[i] = c->next_wire++;
    }
    
    uint32_t gates_start = c->num_gates;
    
    // Component 1: Sumcheck verification (simplified)
    printf("Adding sumcheck verification...\n");
    uint32_t sumcheck_gates_start = c->num_gates;
    
    // For each of 18 rounds, verify polynomial consistency
    uint32_t sumcheck_valid = c->one_wire;
    for (int round = 0; round < 18; round++) {
        // Each round needs:
        // - Extract coefficients from proof (4 * 128 bits)
        // - Generate challenge (SHA3)
        // - Verify polynomial sum
        // - Update running claim
        
        // Simplified: just do a few operations
        uint32_t round_data[4][GF128_BITS];
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < GF128_BITS; j++) {
                round_data[i][j] = proof_wires[(round * 4 * GF128_BITS + i * GF128_BITS + j) % PROOF_SIZE_BITS];
            }
        }
        
        // Add p(0) and p(1)
        uint32_t p0[GF128_BITS], p1[GF128_BITS], sum[GF128_BITS];
        memcpy(p0, round_data[0], GF128_BITS * sizeof(uint32_t));
        memcpy(p1, round_data[0], GF128_BITS * sizeof(uint32_t));
        
        // p(1) = c0 + c1 + c2 + c3
        for (int i = 1; i < 4; i++) {
            add_gf128_add(c, p1, round_data[i], p1);
        }
        
        // sum = p(0) + p(1)
        add_gf128_add(c, p0, p1, sum);
        
        // For now, just check if sum[0] is 0
        uint32_t round_check = gate_not(c, sum[0]);
        
        uint32_t new_valid = wire_new(c);
        gate_and(c, sumcheck_valid, round_check, new_valid);
        sumcheck_valid = new_valid;
    }
    
    uint32_t sumcheck_gates = c->num_gates - sumcheck_gates_start;
    printf("  Sumcheck gates: %u\n", sumcheck_gates);
    
    // Component 2: FRI verification (simplified)
    printf("\nAdding FRI verification...\n");
    uint32_t fri_gates_start = c->num_gates;
    
    uint32_t fri_valid = c->one_wire;
    
    // For each of 200 queries
    for (int q = 0; q < 200; q++) {
        // Each query needs:
        // - Merkle path verification (multiple rounds)
        // - Folding consistency check
        // - Final polynomial evaluation
        
        // Simplified: just do one check per query
        uint32_t query_idx = proof_wires[(1000000 + q * 1000) % PROOF_SIZE_BITS];
        uint32_t query_valid = gate_not(c, query_idx);  // Check if 0
        
        uint32_t new_valid = wire_new(c);
        gate_and(c, fri_valid, query_valid, new_valid);
        fri_valid = new_valid;
        
        // Add some Merkle path verification gates
        for (int level = 0; level < 20; level++) {  // Binary tree depth
            // Hash operation (simplified)
            uint32_t hash_result = add_sha3_256(c, &proof_wires[(q * 1000 + level * 256) % PROOF_SIZE_BITS], 256);
            
            // Compare with expected
            uint32_t hash_valid = gate_not(c, hash_result);
            
            new_valid = wire_new(c);
            gate_and(c, fri_valid, hash_valid, new_valid);
            fri_valid = new_valid;
        }
    }
    
    uint32_t fri_gates = c->num_gates - fri_gates_start;
    printf("  FRI gates: %u\n", fri_gates);
    
    // Component 3: Final combination
    printf("\nCombining results...\n");
    uint32_t final_valid = wire_new(c);
    gate_and(c, sumcheck_valid, fri_valid, final_valid);
    
    // Outputs: validity bit + public input pass-through
    uint32_t num_outputs = 1 + PUBLIC_INPUT_BITS;
    
    // Summary
    printf("\n=== Circuit Statistics ===\n");
    printf("Total inputs:  %u bits\n", num_inputs);
    printf("Total outputs: %u bits\n", num_outputs);
    printf("Total gates:   %u\n", c->num_gates);
    printf("Total wires:   %u\n", c->next_wire);
    printf("\nGate breakdown:\n");
    printf("  Sumcheck:    %u gates (%.1f%%)\n", sumcheck_gates, 100.0 * sumcheck_gates / c->num_gates);
    printf("  FRI:         %u gates (%.1f%%)\n", fri_gates, 100.0 * fri_gates / c->num_gates);
    printf("  Other:       %u gates\n", c->num_gates - sumcheck_gates - fri_gates);
    
    // Write header
    fseek(c->file, 0, SEEK_SET);
    fprintf(c->file, "%u %u %u", num_inputs, num_outputs, c->num_gates);
    
    free(proof_wires);
    free(public_wires);
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        LOG_ERROR("basefold_verifier", "Usage: %s <output_file>\n", argv[0]);
        return 1;
    }
    
    circuit_t* c = circuit_create(argv[1]);
    if (!c) {
        LOG_ERROR("basefold_verifier", "Error: Cannot create circuit file\n");
        return 1;
    }
    
    build_verification_circuit(c);
    
    fclose(c->file);
    free(c);
    
    printf("\nCircuit written to %s\n", argv[1]);
    return 0;
}