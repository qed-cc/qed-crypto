#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include "src/sha3_final.h"
#include "logger.h"

// For simplicity, this example uses a fixed input
const char *test_input = "abc";

int main() {
    printf("=== SHA3-256 Circuit Trace Evaluation ===\n\n");
    
    // Generate SHA3-256 circuit
    printf("Generating SHA3-256 circuit...\n");
    circuit_t *circuit = generate_sha3_circuit(SHA3_256);
    if (!circuit) {
        LOG_ERROR("trace_eval", "Failed to generate SHA3-256 circuit");
        return 1;
    }
    
    printf("SHA3-256 circuit generated with %u gates across %u layers\n", 
           circuit->num_gates, circuit->num_layers);
    
    // Prepare input bits (with padding handled internally)
    size_t input_len = strlen(test_input);
    printf("\nInput: \"%s\" (length: %zu bytes)\n", test_input, input_len);
    
    // Convert input to bits
    uint8_t *input_bits = malloc(1090 * sizeof(uint8_t)); // 1088 (rate) + 2 (domain separator bits)
    if (!input_bits) {
        LOG_ERROR("trace_eval", "Failed to allocate memory for input bits");
        evaluator_free_circuit(circuit);
        return 1;
    }
    
    // Initialize all bits to zero
    memset(input_bits, 0, 1090 * sizeof(uint8_t));
    
    // Set the first two bits (domain separator) to 0 and 1 (for SHA3-256)
    input_bits[0] = 0; // First bit of domain separator (0 for SHA3)
    input_bits[1] = 1; // Second bit of domain separator (1 for SHA3)
    
    // Convert input bytes to bits (MSB first)
    for (size_t i = 0; i < input_len; i++) {
        for (int j = 0; j < 8; j++) {
            input_bits[2 + i * 8 + j] = (test_input[i] >> (7 - j)) & 1;
        }
    }
    
    // Add padding bits (domain separator 0x06 and end bit 0x80)
    // Note: This is a bit simplified - the full SHA3 uses a more complex padding
    input_bits[2 + input_len * 8] = 1; // First padding bit (0x06 = 0b0110)
    input_bits[2 + input_len * 8 + 1] = 1;
    input_bits[2 + input_len * 8 + 2] = 0;
    input_bits[2 + input_len * 8 + 3] = 0;
    
    // Set the end bit (last bit in the block)
    input_bits[1089] = 1; // End bit 0x80 (MSB first, so it's the last bit)
    
    // Prepare for evaluation
    wire_state_t *state = evaluator_init_wire_state(circuit);
    if (!state) {
        LOG_ERROR("trace_eval", "Failed to initialize evaluation state");
        free(input_bits);
        evaluator_free_circuit(circuit);
        return 1;
    }
    
    // Set the input bits
    if (!evaluator_set_inputs(state, input_bits, circuit->num_inputs)) {
        LOG_ERROR("trace_eval", "Failed to set inputs");
        free(input_bits);
        evaluator_free_circuit(circuit);
        evaluator_free_wire_state(state);
        return 1;
    }
    
    // Track layer statistics
    uint32_t *gates_per_layer = calloc(circuit->num_layers, sizeof(uint32_t));
    uint32_t *and_gates_per_layer = calloc(circuit->num_layers, sizeof(uint32_t));
    uint32_t *xor_gates_per_layer = calloc(circuit->num_layers, sizeof(uint32_t));
    
    if (!gates_per_layer || !and_gates_per_layer || !xor_gates_per_layer) {
        LOG_ERROR("trace_eval", "Failed to allocate memory for layer statistics");
        free(input_bits);
        evaluator_free_circuit(circuit);
        evaluator_free_wire_state(state);
        return 1;
    }
    
    // Count gates per layer
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        uint32_t layer = 0;
        // Find which layer this gate is in
        for (uint32_t l = 0; l < circuit->num_layers; l++) {
            if (i >= circuit->layer_offsets[l] && 
                (l == circuit->num_layers - 1 || i < circuit->layer_offsets[l + 1])) {
                layer = l;
                break;
            }
        }
        
        gates_per_layer[layer]++;
        if (circuit->gates[i].type == GATE_AND) {
            and_gates_per_layer[layer]++;
        } else if (circuit->gates[i].type == GATE_XOR) {
            xor_gates_per_layer[layer]++;
        }
    }
    
    // Perform evaluation with timing
    printf("\nEvaluating SHA3-256 circuit...\n");
    clock_t start = clock();
    
    if (!evaluator_evaluate_circuit(circuit, state)) {
        LOG_ERROR("trace_eval", "Failed to evaluate circuit");
        free(input_bits);
        free(gates_per_layer);
        free(and_gates_per_layer);
        free(xor_gates_per_layer);
        evaluator_free_circuit(circuit);
        evaluator_free_wire_state(state);
        return 1;
    }
    
    clock_t end = clock();
    double cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    
    // Get output bits
    uint8_t output_bits[256];
    if (!evaluator_get_outputs(circuit, state, output_bits)) {
        LOG_ERROR("trace_eval", "Failed to get outputs");
        free(input_bits);
        free(gates_per_layer);
        free(and_gates_per_layer);
        free(xor_gates_per_layer);
        evaluator_free_circuit(circuit);
        evaluator_free_wire_state(state);
        return 1;
    }
    
    // Convert output bits to bytes
    uint8_t output[32];
    for (int i = 0; i < 32; i++) {
        output[i] = 0;
        for (int j = 0; j < 8; j++) {
            output[i] |= (output_bits[i * 8 + j] << (7 - j));
        }
    }
    
    // Print output hash
    printf("\nSHA3-256 hash: ");
    for (int i = 0; i < 32; i++) {
        printf("%02x", output[i]);
    }
    printf("\n");
    
    // Print evaluation statistics
    printf("\nEvaluation Statistics:\n");
    printf("Evaluation time: %.6f seconds\n", cpu_time_used);
    printf("Performance: %.2f gates/second\n", circuit->num_gates / cpu_time_used);
    
    // Print layer statistics
    printf("\nLayer Statistics:\n");
    printf("Layer\tTotal Gates\tAND Gates\tXOR Gates\n");
    printf("-----\t-----------\t---------\t---------\n");
    
    for (uint32_t i = 0; i < circuit->num_layers; i++) {
        printf("%5u\t%11u\t%9u\t%9u\n", 
               i, gates_per_layer[i], and_gates_per_layer[i], xor_gates_per_layer[i]);
        
        // Print only first 10 layers, then summary
        if (i == 9 && circuit->num_layers > 20) {
            printf("  ... %u more layers ...\n", circuit->num_layers - 20);
            i = circuit->num_layers - 11; // Show last 10 layers
        }
    }
    
    // Clean up
    free(input_bits);
    free(gates_per_layer);
    free(and_gates_per_layer);
    free(xor_gates_per_layer);
    evaluator_free_circuit(circuit);
    evaluator_free_wire_state(state);
    
    return 0;
}