/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Example: Loading and Proving RISC-V Compiled Circuits
 * 
 * This example demonstrates how to:
 * 1. Load a circuit compiled by the RISC-V compiler
 * 2. Set up inputs properly
 * 3. Generate a zero-knowledge proof
 * 4. Verify the proof
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../apps/gate_computer/src/circuit_format.h"
#include "../apps/gate_computer/src/evaluator.h"
#include "../modules/basefold/include/basefold_trace.h"
#include "logger.h"
#include "input_validation.h"

// Example: Load and prove a simple addition circuit from RISC-V
int main(int argc, char** argv) {
    if (argc < 2) {
        LOG_INFO("riscv_integration_example", "Usage: %s <circuit_file>\n", argv[0]);
        LOG_INFO("riscv_integration_example", "Example: %s add_circuit.bin\n", argv[0]);
        return 1;
    }

    // Validate circuit file path
    if (validate_file_path(argv[1], true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("riscv_example", "Invalid circuit file path: %s", argv[1]);
        return 1;
    }

    // Step 1: Load the circuit
    LOG_INFO("riscv_integration_example", "Loading RISC-V circuit from %s...\n", argv[1]);
    circuit_t* circuit = load_circuit_from_file(argv[1]);
    if (!circuit) {
        LOG_ERROR("riscv_example", "Failed to load circuit");
        return 1;
    }

    LOG_INFO("riscv_integration_example", "Circuit loaded:\n");
    LOG_INFO("riscv_integration_example", "  Inputs: %u bits\n", circuit->num_inputs);
    LOG_INFO("riscv_integration_example", "  Outputs: %u bits\n", circuit->num_outputs);
    LOG_INFO("riscv_integration_example", "  Gates: %u\n", circuit->num_gates);

    // Step 2: Set up inputs
    // For RISC-V circuits, inputs are laid out as:
    // - Bits 0-1: Constants (handled internally)
    // - Bits 2-33: Program Counter (32 bits)
    // - Bits 34-1057: Registers (32 registers × 32 bits)
    // - Bits 1058+: Memory

    uint8_t* inputs = calloc(circuit->num_inputs, sizeof(uint8_t));
    if (!inputs) {
        LOG_ERROR("riscv_example", "Failed to allocate inputs");
        evaluator_free_circuit(circuit);
        return 1;
    }
    
    // Example: Set initial PC to 0
    // PC bits start at index 2
    for (int i = 0; i < 32; i++) {
        inputs[2 + i] = 0;
    }

    // Example: Set register values
    // Let's set x1 = 5 and x2 = 3 for an ADD operation
    // x1 starts at bit 34 + 32 = 66
    inputs[66] = 1;  // bit 0 of x1
    inputs[68] = 1;  // bit 2 of x1 (5 = 0b101)
    
    // x2 starts at bit 34 + 64 = 98  
    inputs[98] = 1;  // bit 0 of x2
    inputs[99] = 1;  // bit 1 of x2 (3 = 0b11)

    // Step 3: Evaluate the circuit
    LOG_INFO("riscv_integration_example", "\nEvaluating circuit...\n");
    circuit_evaluator_t* evaluator = create_circuit_evaluator(circuit);
    
    uint8_t* outputs = malloc(circuit->num_outputs * sizeof(uint8_t));
    evaluate_circuit(evaluator, inputs, outputs);

    // Print some output bits (e.g., result register)
    LOG_INFO("riscv_integration_example", "Output bits (first 32): ");
    for (int i = 0; i < 32 && i < circuit->num_outputs; i++) {
        LOG_INFO("riscv_integration_example", "%d", outputs[i]);
    }
    LOG_INFO("riscv_integration_example", "\n");

    // Step 4: Generate zero-knowledge proof
    LOG_INFO("riscv_integration_example", "\nGenerating zero-knowledge proof...\n");
    
    // Create proof configuration
    basefold_proof_config_t config = {
        .security_bits = 128,
        .num_variables = count_variables(circuit->num_gates),
        .enable_zk = true
    };

    // Generate the proof
    basefold_proof_t* proof = basefold_prove(circuit, inputs, &config);
    if (!proof) {
        LOG_ERROR("riscv_example", "Failed to generate proof");
        return 1;
    }

    LOG_INFO("riscv_integration_example", "Proof generated successfully!\n");
    LOG_INFO("riscv_integration_example", "  Proof size: ~%zu KB\n", basefold_proof_size(proof) / 1024);

    // Step 5: Verify the proof
    LOG_INFO("riscv_integration_example", "\nVerifying proof...\n");
    
    // Verifier only needs the circuit structure and public outputs
    bool valid = basefold_verify(circuit, outputs, proof, &config);
    
    if (valid) {
        LOG_INFO("riscv_integration_example", "✅ Proof verified successfully!\n");
    } else {
        LOG_INFO("riscv_integration_example", "❌ Proof verification failed!\n");
    }

    // Step 6: Save proof to file
    const char* proof_file = "riscv_proof.bfp";
    FILE* f = fopen(proof_file, "wb");
    if (f) {
        basefold_proof_write(proof, f);
        fclose(f);
        LOG_INFO("riscv_integration_example", "\nProof saved to %s\n", proof_file);
    }

    // Cleanup
    free(inputs);
    free(outputs);
    free_circuit(circuit);
    free_evaluator(evaluator);
    basefold_proof_free(proof);

    return valid ? 0 : 1;
}

/*
 * To compile and run this example:
 * 
 * 1. First, create a RISC-V circuit:
 *    cd modules/riscv_compiler
 *    ./scripts/compile_to_circuit.sh examples/add.c -o add_circuit.bin
 * 
 * 2. Compile this example:
 *    gcc -o riscv_example riscv_integration_example.c \
 *        -L../build/lib -lgate_computer -lbasefold -lgf128 -lsha3 -lm
 * 
 * 3. Run it:
 *    ./riscv_example add_circuit.bin
 * 
 * The example will:
 * - Load the circuit
 * - Set up initial register values
 * - Evaluate the circuit
 * - Generate a ZK proof
 * - Verify the proof
 * - Save the proof to disk
 */

/*
 * Notes for extending this:
 * 
 * 1. Memory initialization:
 *    For circuits that use memory, initialize memory bits starting
 *    at index 1058 + num_registers * 32
 * 
 * 2. Public vs Private inputs:
 *    Currently all inputs are private. To make some public,
 *    we need to extend the circuit format and proof system.
 * 
 * 3. Debugging:
 *    Use --trace-eval flag in gate_computer to see gate-by-gate evaluation
 * 
 * 4. Performance:
 *    For large circuits (>1M gates), consider:
 *    - Streaming evaluation
 *    - Parallel proof generation
 *    - Memory-mapped circuit files
 */