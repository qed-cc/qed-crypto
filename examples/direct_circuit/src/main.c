#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

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
    // Create a circuit with 2 inputs, 1 gate, and 1 output
    circuit_t *circuit = evaluator_init_circuit(2, 1, 1);
    if (!circuit) {
        LOG_INFO("main", "Failed to initialize circuit\n");
        return NULL;
    }
    
    // Input wires are 2 and 3 (0 and 1 are constants)
    wire_id_t input1 = 2;
    wire_id_t input2 = 3;
    wire_id_t output = 4;  // First gate output
    
    // Manually add the XOR gate directly to the circuit array
    circuit->gates[0].type = GATE_XOR;
    circuit->gates[0].input1 = input1;
    circuit->gates[0].input2 = input2;
    circuit->gates[0].output = output;
    
    // Set the output wire
    circuit->output_wires[0] = output;
    
    // Prepare the circuit for evaluation
    if (!evaluator_prepare_circuit(circuit)) {
        LOG_INFO("main", "Failed to prepare circuit\n");
        evaluator_free_circuit(circuit);
        return NULL;
    }
    
    return circuit;
}

// Example 2: Build a half adder circuit (sum and carry)
circuit_t* build_half_adder() {
    // Create a circuit with 2 inputs, 2 gates, and 2 outputs
    circuit_t *circuit = evaluator_init_circuit(2, 2, 2);
    if (!circuit) {
        LOG_INFO("main", "Failed to initialize circuit\n");
        return NULL;
    }
    
    // Input wires are 2 and 3 (0 and 1 are constants)
    wire_id_t input1 = 2;
    wire_id_t input2 = 3;
    wire_id_t sum = 4;     // First gate output (XOR)
    wire_id_t carry = 5;   // Second gate output (AND)
    
    // Manually add the XOR gate for sum
    circuit->gates[0].type = GATE_XOR;
    circuit->gates[0].input1 = input1;
    circuit->gates[0].input2 = input2;
    circuit->gates[0].output = sum;
    
    // Manually add the AND gate for carry
    circuit->gates[1].type = GATE_AND;
    circuit->gates[1].input1 = input1;
    circuit->gates[1].input2 = input2;
    circuit->gates[1].output = carry;
    
    // Set the output wires (sum first, then carry)
    circuit->output_wires[0] = sum;
    circuit->output_wires[1] = carry;
    
    // Prepare the circuit for evaluation
    if (!evaluator_prepare_circuit(circuit)) {
        LOG_INFO("main", "Failed to prepare circuit\n");
        evaluator_free_circuit(circuit);
        return NULL;
    }
    
    return circuit;
}

// Example 3: Build a full adder circuit
circuit_t* build_full_adder() {
    // Create a circuit with 3 inputs, 5 gates, and 2 outputs
    circuit_t *circuit = evaluator_init_circuit(3, 5, 2);
    if (!circuit) {
        LOG_INFO("main", "Failed to initialize circuit\n");
        return NULL;
    }
    
    // Input wires are 2, 3, and 4 (0 and 1 are constants)
    wire_id_t a = 2;
    wire_id_t b = 3;
    wire_id_t cin = 4;
    
    // Gates for first half adder (a + b)
    wire_id_t sum1 = 5;    // a XOR b
    wire_id_t carry1 = 6;  // a AND b
    
    // Gates for second half adder (sum1 + cin)
    wire_id_t sum2 = 7;    // sum1 XOR cin (final sum)
    wire_id_t carry2 = 8;  // sum1 AND cin
    
    // Gate for OR of carries (final carry out)
    wire_id_t cout = 9;    // carry1 OR carry2 implemented as XOR of 
                          // (carry1 XOR carry2) and (carry1 AND carry2)
    
    // Manually add gates
    
    // First half adder - XOR gate
    circuit->gates[0].type = GATE_XOR;
    circuit->gates[0].input1 = a;
    circuit->gates[0].input2 = b;
    circuit->gates[0].output = sum1;
    
    // First half adder - AND gate
    circuit->gates[1].type = GATE_AND;
    circuit->gates[1].input1 = a;
    circuit->gates[1].input2 = b;
    circuit->gates[1].output = carry1;
    
    // Second half adder - XOR gate
    circuit->gates[2].type = GATE_XOR;
    circuit->gates[2].input1 = sum1;
    circuit->gates[2].input2 = cin;
    circuit->gates[2].output = sum2;
    
    // Second half adder - AND gate
    circuit->gates[3].type = GATE_AND;
    circuit->gates[3].input1 = sum1;
    circuit->gates[3].input2 = cin;
    circuit->gates[3].output = carry2;
    
    // OR implementation (carry1 OR carry2) via XOR of XOR and AND
    // Since we only have AND and XOR gates, we implement OR as:
    // a OR b = a XOR b XOR (a AND b)
    // In this case: carry1 OR carry2 = carry1 XOR carry2 XOR (carry1 AND carry2)
    // Simplified to one step because both carry1 and carry2 can't be 1 
    // at the same time in this circuit
    circuit->gates[4].type = GATE_XOR;
    circuit->gates[4].input1 = carry1;
    circuit->gates[4].input2 = carry2;
    circuit->gates[4].output = cout;
    
    // Set the output wires (sum first, then carry out)
    circuit->output_wires[0] = sum2;
    circuit->output_wires[1] = cout;
    
    // Prepare the circuit for evaluation
    if (!evaluator_prepare_circuit(circuit)) {
        LOG_INFO("main", "Failed to prepare circuit\n");
        evaluator_free_circuit(circuit);
        return NULL;
    }
    
    return circuit;
}

int main() {
    LOG_INFO("main", "=== Gate Computer Direct Circuit Examples ===\n\n");
    
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