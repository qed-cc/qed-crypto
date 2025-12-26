#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "circuit_generator.h"
#include "evaluator.h"

// Function to print circuit details
void print_circuit_info(circuit_t *circuit) {
    LOG_INFO("main", "Circuit Information:\n");
    LOG_INFO("main", "  Number of inputs: %u\n", circuit->num_inputs);
    LOG_INFO("main", "  Number of gates: %u\n", circuit->num_gates);
    LOG_INFO("main", "  Number of outputs: %u\n", circuit->num_outputs);
    LOG_INFO("main", "  Number of layers: %u\n", circuit->num_layers);
    
    LOG_INFO("main", "\nGates:\n");
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t gate = circuit->gates[i];
        LOG_INFO("main", "  Gate %u: Type=%s, Input1=%u, Input2=%u, Output=%u\n", 
               i, 
               gate.type == GATE_AND ? "AND" : "XOR",
               gate.input1, gate.input2, gate.output);
    }
    
    LOG_INFO("main", "\nOutputs:\n");
    for (uint32_t i = 0; i < circuit->num_outputs; i++) {
        LOG_INFO("main", "  Output %u: Wire ID=%u\n", i, circuit->output_wires[i]);
    }
}

// Function to evaluate circuit with given inputs and print outputs
void evaluate_and_print(circuit_t *circuit, uint8_t *inputs, uint32_t num_inputs) {
    // Initialize wire state
    wire_state_t *state = evaluator_init_wire_state(circuit);
    if (!state) {
        LOG_INFO("main", "Failed to initialize wire state\n");
        return;
    }
    
    // Set inputs
    if (!evaluator_set_inputs(state, inputs, num_inputs)) {
        LOG_INFO("main", "Failed to set inputs\n");
        evaluator_free_wire_state(state);
        return;
    }
    
    // Print inputs
    LOG_INFO("main", "\nInputs: ");
    for (uint32_t i = 0; i < num_inputs; i++) {
        LOG_INFO("main", "%u ", inputs[i]);
    }
    LOG_INFO("main", "\n");
    
    // Evaluate circuit
    if (!evaluator_evaluate_circuit(circuit, state)) {
        LOG_INFO("main", "Failed to evaluate circuit\n");
        evaluator_free_wire_state(state);
        return;
    }
    
    // Get outputs
    uint8_t *outputs = (uint8_t *)malloc(circuit->num_outputs * sizeof(uint8_t));
    if (!outputs) {
        LOG_INFO("main", "Failed to allocate memory for outputs\n");
        evaluator_free_wire_state(state);
        return;
    }
    
    if (!evaluator_get_outputs(circuit, state, outputs)) {
        LOG_INFO("main", "Failed to get outputs\n");
        free(outputs);
        evaluator_free_wire_state(state);
        return;
    }
    
    // Print outputs
    LOG_INFO("main", "Outputs: ");
    for (uint32_t i = 0; i < circuit->num_outputs; i++) {
        LOG_INFO("main", "%u ", outputs[i]);
    }
    LOG_INFO("main", "\n");
    
    // Clean up
    free(outputs);
    evaluator_free_wire_state(state);
}

// Example 1: Build a simple XOR circuit (implements XOR of two bits)
circuit_t* build_xor_circuit() {
    // Create a circuit builder with 2 inputs and initial capacity for 10 gates
    circuit_builder_t *builder = circuit_generator_create(2, 10);
    if (!builder) {
        LOG_INFO("main", "Failed to create circuit builder\n");
        return NULL;
    }
    
    // Input wires are 2 and 3 (0 and 1 are constants)
    wire_id_t input1 = 2;
    wire_id_t input2 = 3;
    
    // Add an XOR gate
    wire_id_t output = circuit_generator_add_xor(builder, input1, input2);
    if (output == 0) {
        LOG_INFO("main", "Failed to add XOR gate: %s\n", circuit_generator_get_error());
        circuit_generator_free(builder);
        return NULL;
    }
    
    // Set the output wire
    wire_id_t outputs[] = {output};
    circuit_t *circuit = circuit_generator_finalize(builder, outputs, 1);
    
    // Free the builder (circuit is now owned by the caller)
    circuit_generator_free(builder);
    
    return circuit;
}

// Example 2: Build a half adder circuit (sum and carry)
circuit_t* build_half_adder() {
    // Create a circuit builder with 2 inputs and initial capacity for 10 gates
    circuit_builder_t *builder = circuit_generator_create(2, 10);
    if (!builder) {
        LOG_INFO("main", "Failed to create circuit builder\n");
        return NULL;
    }
    
    // Input wires are 2 and 3 (0 and 1 are constants)
    wire_id_t input1 = 2;
    wire_id_t input2 = 3;
    
    // Create a half adder
    wire_id_t sum = 0;
    wire_id_t carry = 0;
    
    if (!circuit_generator_half_adder(builder, input1, input2, &sum, &carry)) {
        LOG_INFO("main", "Failed to build half adder: %s\n", circuit_generator_get_error());
        circuit_generator_free(builder);
        return NULL;
    }
    
    // Set the output wires (sum first, then carry)
    wire_id_t outputs[] = {sum, carry};
    circuit_t *circuit = circuit_generator_finalize(builder, outputs, 2);
    
    // Free the builder (circuit is now owned by the caller)
    circuit_generator_free(builder);
    
    return circuit;
}

// Example 3: Build a full adder circuit
circuit_t* build_full_adder() {
    // Create a circuit builder with 3 inputs and initial capacity for 20 gates
    circuit_builder_t *builder = circuit_generator_create(3, 20);
    if (!builder) {
        LOG_INFO("main", "Failed to create circuit builder\n");
        return NULL;
    }
    
    // Input wires are 2, 3, and 4 (0 and 1 are constants)
    wire_id_t a = 2;
    wire_id_t b = 3;
    wire_id_t cin = 4;
    
    // Create a full adder
    wire_id_t sum = 0;
    wire_id_t cout = 0;
    
    if (!circuit_generator_full_adder(builder, a, b, cin, &sum, &cout)) {
        LOG_INFO("main", "Failed to build full adder: %s\n", circuit_generator_get_error());
        circuit_generator_free(builder);
        return NULL;
    }
    
    // Set the output wires (sum first, then carry out)
    wire_id_t outputs[] = {sum, cout};
    circuit_t *circuit = circuit_generator_finalize(builder, outputs, 2);
    
    // Free the builder (circuit is now owned by the caller)
    circuit_generator_free(builder);
    
    return circuit;
}

int main() {
    LOG_INFO("main", "=== Gate Computer Circuit Examples ===\n\n");
    
    // Example 1: XOR Circuit
    LOG_INFO("main", "--- Example 1: XOR Circuit ---\n");
    circuit_t *xor_circuit = build_xor_circuit();
    if (xor_circuit) {
        print_circuit_info(xor_circuit);
        
        // Evaluate with different inputs
        uint8_t inputs1[] = {0, 0};
        uint8_t inputs2[] = {0, 1};
        uint8_t inputs3[] = {1, 0};
        uint8_t inputs4[] = {1, 1};
        
        evaluate_and_print(xor_circuit, inputs1, 2);
        evaluate_and_print(xor_circuit, inputs2, 2);
        evaluate_and_print(xor_circuit, inputs3, 2);
        evaluate_and_print(xor_circuit, inputs4, 2);
        
        // Clean up
        evaluator_free_circuit(xor_circuit);
    }
    
    LOG_INFO("main", "\n--- Example 2: Half Adder Circuit ---\n");
    circuit_t *half_adder = build_half_adder();
    if (half_adder) {
        print_circuit_info(half_adder);
        
        // Evaluate with different inputs
        uint8_t inputs1[] = {0, 0};
        uint8_t inputs2[] = {0, 1};
        uint8_t inputs3[] = {1, 0};
        uint8_t inputs4[] = {1, 1};
        
        evaluate_and_print(half_adder, inputs1, 2);
        evaluate_and_print(half_adder, inputs2, 2);
        evaluate_and_print(half_adder, inputs3, 2);
        evaluate_and_print(half_adder, inputs4, 2);
        
        // Clean up
        evaluator_free_circuit(half_adder);
    }
    
    LOG_INFO("main", "\n--- Example 3: Full Adder Circuit ---\n");
    circuit_t *full_adder = build_full_adder();
    if (full_adder) {
        print_circuit_info(full_adder);
        
        // Evaluate with different inputs (a, b, cin)
        uint8_t inputs1[] = {0, 0, 0};
        uint8_t inputs2[] = {0, 0, 1};
        uint8_t inputs3[] = {0, 1, 0};
        uint8_t inputs4[] = {0, 1, 1};
        uint8_t inputs5[] = {1, 0, 0};
        uint8_t inputs6[] = {1, 0, 1};
        uint8_t inputs7[] = {1, 1, 0};
        uint8_t inputs8[] = {1, 1, 1};
        
        evaluate_and_print(full_adder, inputs1, 3);
        evaluate_and_print(full_adder, inputs2, 3);
        evaluate_and_print(full_adder, inputs3, 3);
        evaluate_and_print(full_adder, inputs4, 3);
        evaluate_and_print(full_adder, inputs5, 3);
        evaluate_and_print(full_adder, inputs6, 3);
        evaluate_and_print(full_adder, inputs7, 3);
        evaluate_and_print(full_adder, inputs8, 3);
        
        // Clean up
        evaluator_free_circuit(full_adder);
    }
    
    return 0;
}