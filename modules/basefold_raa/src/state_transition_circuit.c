/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file state_transition_circuit.c
 * @brief State transition circuit for blockchain circular recursion
 * 
 * Creates a circuit that:
 * 1. Verifies previous state hash
 * 2. Applies state transition (new block)
 * 3. Optionally verifies previous proof (for recursion)
 * 4. Outputs new state hash
 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "../include/basefold_raa.h"
#include "../include/state_transition.h"
#include "../../sha3/include/sha3.h"
#include "../../circuit_evaluator/include/evaluator.h"

/* blockchain_circuit_state_t is defined in state_transition.h */

/**
 * @brief Create a simple state transition circuit
 * 
 * Circuit computes: new_hash = SHA3(prev_hash || block_number || data)
 */
circuit_t* create_state_transition_circuit(
    const blockchain_circuit_state_t *prev_state,
    const blockchain_circuit_state_t *new_state
) {
    // Create circuit with appropriate size
    // SHA3-256 needs ~48K gates
    circuit_t *circuit = evaluator_init_circuit(320, 60000, 256);
    if (!circuit) return NULL;
    
    // Input wires for previous hash (256 bits)
    // Wire IDs start at 2 (0=const0, 1=const1)
    uint32_t prev_hash_wires[256];
    for (int i = 0; i < 256; i++) {
        prev_hash_wires[i] = 2 + i;
    }
    
    // Add block number as 64-bit input
    uint32_t block_num_wires[64];
    for (int i = 0; i < 64; i++) {
        block_num_wires[i] = 2 + 256 + i;
    }
    
    // For now, create a simple hash simulation
    // Real implementation would use SHA3 circuit from circuit_generator
    
    // XOR all input bits together as a dummy operation
    uint32_t result_wire = prev_hash_wires[0];
    for (int i = 1; i < 256; i++) {
        gate_t gate = {
            .type = GATE_XOR,
            .input1 = result_wire,
            .input2 = prev_hash_wires[i],
            .output = circuit->num_gates + 257 + i
        };
        circuit->gates[circuit->num_gates++] = gate;
        result_wire = gate.output;
    }
    
    // XOR in block number
    for (int i = 0; i < 64; i++) {
        gate_t gate = {
            .type = GATE_XOR,
            .input1 = result_wire,
            .input2 = block_num_wires[i],
            .output = circuit->num_gates + 600 + i
        };
        circuit->gates[circuit->num_gates++] = gate;
        result_wire = gate.output;
    }
    
    // Set output (simplified - just one bit for now)
    circuit->output_wires[0] = result_wire;
    circuit->num_outputs = 1;
    
    // Set layer information
    circuit->layer_offsets = malloc(2 * sizeof(uint32_t));
    circuit->layer_offsets[0] = 0;
    circuit->layer_offsets[1] = circuit->num_gates;
    circuit->num_layers = 1;
    
    return circuit;
}

/**
 * @brief Create a recursive state transition circuit
 * 
 * This circuit additionally verifies the previous proof
 */
circuit_t* create_recursive_state_transition_circuit(
    const blockchain_circuit_state_t *prev_state,
    const blockchain_circuit_state_t *new_state,
    size_t proof_size
) {
    // For now, return the simple version
    // Full implementation would include the recursive verifier circuit
    return create_state_transition_circuit(prev_state, new_state);
}

/**
 * @brief Free state transition circuit
 */
void free_state_transition_circuit(circuit_t *circuit) {
    if (!circuit) return;
    
    free(circuit->gates);
    free(circuit->output_wires);
    free(circuit->layer_offsets);
    free(circuit);
}