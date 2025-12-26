/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file circuit_witness_generator.c
 * @brief Generate valid witnesses for circuits that satisfy sumcheck
 * 
 * A witness is the evaluation of a circuit on all 2^n possible inputs.
 * For sumcheck to verify, the witness must encode actual circuit computations.
 */

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "../include/basefold_raa.h"
#include "../../circuit_evaluator/include/evaluator.h"
#include "../../gf128/include/gf128.h"

/**
 * @brief Evaluate a single gate
 */
static uint8_t evaluate_gate(const gate_t *gate, const uint8_t *wire_values) {
    uint8_t in1 = wire_values[gate->input1];
    uint8_t in2 = wire_values[gate->input2];
    
    if (gate->type == GATE_AND) {
        return in1 & in2;
    } else { // GATE_XOR
        return in1 ^ in2;
    }
}

/**
 * @brief Evaluate circuit on a single input assignment
 * 
 * @param circuit The circuit to evaluate
 * @param input_bits Input assignment (num_inputs bits)
 * @param wire_values Working space for wire values (must be large enough)
 * @return Output value (we assume single output for now)
 */
static uint8_t evaluate_circuit_single(
    const circuit_t *circuit,
    const uint8_t *input_bits,
    uint8_t *wire_values
) {
    // Set constant wires
    wire_values[0] = 0;  // Constant 0
    wire_values[1] = 1;  // Constant 1
    
    // Set input wires (starting at wire 2)
    for (uint32_t i = 0; i < circuit->num_inputs; i++) {
        wire_values[2 + i] = input_bits[i];
    }
    
    // Evaluate gates in topological order
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        const gate_t *gate = &circuit->gates[i];
        wire_values[gate->output] = evaluate_gate(gate, wire_values);
    }
    
    // Return first output (extend for multiple outputs if needed)
    return wire_values[circuit->output_wires[0]];
}

/**
 * @brief Generate witness by evaluating circuit on all 2^n inputs
 * 
 * The witness is a multilinear polynomial's evaluations on the boolean hypercube.
 * witness[i] = circuit evaluation on input i (where i is interpreted as bits)
 * 
 * @param circuit Circuit to evaluate
 * @param num_variables Number of input variables (log2 of witness size)
 * @return Witness polynomial or NULL on error
 */
gf128_t* generate_circuit_witness(const circuit_t *circuit, size_t num_variables) {
    if (!circuit || num_variables > 30) {
        return NULL;
    }
    
    size_t witness_size = 1ULL << num_variables;
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) {
        return NULL;
    }
    
    // Allocate working space for wire values
    // Max wire ID is usually num_inputs + num_gates + some extra
    size_t max_wires = 2 + circuit->num_inputs + circuit->num_gates + 1000;
    uint8_t *wire_values = calloc(max_wires, sizeof(uint8_t));
    if (!wire_values) {
        free(witness);
        return NULL;
    }
    
    // Evaluate circuit on all possible inputs
    uint8_t *input_bits = calloc(circuit->num_inputs, sizeof(uint8_t));
    if (!input_bits) {
        free(wire_values);
        free(witness);
        return NULL;
    }
    
    for (size_t i = 0; i < witness_size; i++) {
        // Convert index to input bit assignment
        for (size_t j = 0; j < circuit->num_inputs && j < num_variables; j++) {
            input_bits[j] = (i >> j) & 1;
        }
        
        // Pad with zeros if circuit has fewer inputs than witness variables
        for (size_t j = circuit->num_inputs; j < num_variables; j++) {
            // These extra variables don't affect the circuit output
        }
        
        // Evaluate circuit
        uint8_t output = evaluate_circuit_single(circuit, input_bits, wire_values);
        
        // Convert boolean output to GF128
        if (output) {
            witness[i] = gf128_one();
        } else {
            witness[i] = gf128_zero();
        }
    }
    
    free(input_bits);
    free(wire_values);
    
    return witness;
}

/**
 * @brief Generate witness for identity circuit (for testing)
 * 
 * Identity circuit: output = input[0]
 */
gf128_t* generate_identity_witness(size_t num_variables) {
    size_t witness_size = 1ULL << num_variables;
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) return NULL;
    
    // f(x0, x1, ..., xn) = x0
    for (size_t i = 0; i < witness_size; i++) {
        if (i & 1) {  // Check first bit
            witness[i] = gf128_one();
        } else {
            witness[i] = gf128_zero();
        }
    }
    
    return witness;
}

/**
 * @brief Generate witness for AND of all inputs
 */
gf128_t* generate_and_all_witness(size_t num_variables) {
    size_t witness_size = 1ULL << num_variables;
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) return NULL;
    
    // f(x0, x1, ..., xn) = x0 AND x1 AND ... AND xn
    // Only true when all inputs are 1 (i.e., i = 2^n - 1)
    for (size_t i = 0; i < witness_size; i++) {
        if (i == witness_size - 1) {
            witness[i] = gf128_one();
        } else {
            witness[i] = gf128_zero();
        }
    }
    
    return witness;
}

/**
 * @brief Create a simple test circuit
 */
circuit_t* create_simple_test_circuit(void) {
    // Create circuit: out = in0 XOR in1
    circuit_t *circuit = evaluator_init_circuit(2, 1, 1);
    if (!circuit) return NULL;
    
    // Add single XOR gate
    gate_t gate = {
        .type = GATE_XOR,
        .input1 = 2,  // First input (wire 2)
        .input2 = 3,  // Second input (wire 3)
        .output = 4   // Output wire
    };
    circuit->gates[0] = gate;
    circuit->num_gates = 1;
    
    // Set output
    circuit->output_wires[0] = 4;
    
    return circuit;
}