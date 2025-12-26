#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include "src/sha3_final.h"
#include "logger.h"

int main() {
    printf("=== SHA3-256 Gate Type Analysis ===\n\n");
    
    // Generate SHA3-256 circuit
    printf("Generating SHA3-256 circuit...\n");
    circuit_t *circuit = generate_sha3_circuit(SHA3_FINAL_256);
    if (!circuit) {
        LOG_ERROR("count_gates", "Failed to generate SHA3-256 circuit");
        return 1;
    }
    
    // Count gate types
    uint32_t and_gates = 0;
    uint32_t xor_gates = 0;
    
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        if (circuit->gates[i].type == GATE_AND) {
            and_gates++;
        } else if (circuit->gates[i].type == GATE_XOR) {
            xor_gates++;
        }
    }
    
    // Print statistics
    printf("\nCircuit Statistics:\n");
    printf("Total gates:  %u\n", circuit->num_gates);
    printf("Total layers: %u\n", circuit->num_layers);
    printf("AND gates:    %u (%.2f%%)\n", and_gates, 100.0 * and_gates / circuit->num_gates);
    printf("XOR gates:    %u (%.2f%%)\n", xor_gates, 100.0 * xor_gates / circuit->num_gates);
    
    evaluator_free_circuit(circuit);
    return 0;
}