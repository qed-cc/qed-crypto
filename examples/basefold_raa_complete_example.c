/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Complete BaseFold RAA Example
 * 
 * This example demonstrates:
 * 1. Loading a circuit from file
 * 2. Evaluating the circuit on inputs
 * 3. Generating a zero-knowledge proof
 * 4. Verifying the proof
 * 5. Serializing/deserializing proofs
 */

#include "basefold_raa.h"
#include "circuit_io.h"
#include "circuit_evaluator.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "logger.h"
#include "input_validation.h"

// Helper function to print timing
static double get_time_ms() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        LOG_ERROR("example", "Usage: %s <circuit_file> <input_hex>", argv[0]);
        LOG_ERROR("example", "Example: %s sha3_256.circuit deadbeef", argv[0]);
        return 1;
    }
    
    const char* circuit_file = argv[1];
    const char* input_hex = argv[2];
    
    // Validate command line arguments
    if (validate_file_path(circuit_file, true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("example", "Invalid circuit file path: %s", circuit_file);
        return 1;
    }
    
    if (validate_hex_string(input_hex, 0) != VALIDATION_SUCCESS) {
        LOG_ERROR("example", "Invalid hex input: %s", input_hex);
        return 1;
    }
    
    LOG_INFO("basefold_raa_complete_example", "BaseFold RAA Complete Example\n");
    LOG_INFO("basefold_raa_complete_example", "=============================\n\n");
    
    // Step 1: Load circuit
    LOG_INFO("basefold_raa_complete_example", "1. Loading circuit from %s...\n", circuit_file);
    circuit_t* circuit = circuit_load(circuit_file);
    if (!circuit) {
        LOG_ERROR("example", "Failed to load circuit");
        return 1;
    }
    LOG_INFO("basefold_raa_complete_example", "   - Gates: %zu\n", circuit->num_gates);
    LOG_INFO("basefold_raa_complete_example", "   - Inputs: %zu\n", circuit->num_inputs);
    LOG_INFO("basefold_raa_complete_example", "   - Outputs: %zu\n", circuit->num_outputs);
    
    // Step 2: Parse input
    LOG_INFO("basefold_raa_complete_example", "\n2. Parsing input: %s\n", input_hex);
    size_t input_len = strlen(input_hex) / 2;
    uint8_t* input_bytes = malloc(input_len);
    for (size_t i = 0; i < input_len; i++) {
        sscanf(input_hex + 2*i, "%2hhx", &input_bytes[i]);
    }
    
    // Convert to field elements
    size_t num_input_bits = input_len * 8;
    if (num_input_bits > circuit->num_inputs) {
        LOG_ERROR("example", "Input too large for circuit");
        return 1;
    }
    
    gf128_t* inputs = calloc(circuit->num_inputs, sizeof(gf128_t));
    if (!inputs) {
        LOG_ERROR("example", "Failed to allocate inputs");
        return 1;
    }
    for (size_t i = 0; i < num_input_bits; i++) {
        if ((input_bytes[i/8] >> (i%8)) & 1) {
            inputs[i] = GF128_ONE;
        }
    }
    
    // Step 3: Evaluate circuit
    LOG_INFO("basefold_raa_complete_example", "\n3. Evaluating circuit...\n");
    double eval_start = get_time_ms();
    
    size_t witness_size = circuit->num_inputs + circuit->num_gates;
    gf128_t* witness = calloc(witness_size, sizeof(gf128_t));
    if (!witness) {
        LOG_ERROR("example", "Failed to allocate witness");
        free(inputs);
        return 1;
    }
    
    // Copy inputs to witness
    memcpy(witness, inputs, circuit->num_inputs * sizeof(gf128_t));
    
    // Evaluate gates
    for (size_t i = 0; i < circuit->num_gates; i++) {
        gate_t* gate = &circuit->gates[i];
        gf128_t left = witness[gate->left_input];
        gf128_t right = witness[gate->right_input];
        
        switch (gate->type) {
            case GATE_ADD:
                witness[gate->output] = gf128_add(left, right);
                break;
            case GATE_MUL:
                witness[gate->output] = gf128_mul(left, right);
                break;
            case GATE_XOR:
                witness[gate->output] = gf128_add(left, right);  // Same as ADD in GF(2^128)
                break;
            case GATE_AND:
                witness[gate->output] = gf128_mul(left, right);  // Same as MUL for binary
                break;
        }
    }
    
    double eval_time = get_time_ms() - eval_start;
    LOG_INFO("basefold_raa_complete_example", "   - Evaluation time: %.2f ms\n", eval_time);
    
    // Extract outputs
    LOG_INFO("basefold_raa_complete_example", "   - Output (first 32 bits): ");
    for (size_t i = 0; i < 32 && i < circuit->num_outputs; i++) {
        LOG_INFO("basefold_raa_complete_example", "%d", gf128_eq(witness[circuit->outputs[i]], GF128_ONE) ? 1 : 0);
    }
    LOG_INFO("basefold_raa_complete_example", "...\n");
    
    // Step 4: Generate proof
    LOG_INFO("basefold_raa_complete_example", "\n4. Generating zero-knowledge proof...\n");
    
    // Configure proof system
    size_t num_variables = 0;
    size_t n = witness_size;
    while (n > 1) {
        n >>= 1;
        num_variables++;
    }
    
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .security_level = 128,
        .enable_zk = 1,  // Enable zero-knowledge
        .num_threads = 4
    };
    
    LOG_INFO("basefold_raa_complete_example", "   - Security level: %d bits\n", config.security_level);
    LOG_INFO("basefold_raa_complete_example", "   - Zero-knowledge: %s\n", config.enable_zk ? "enabled" : "disabled");
    LOG_INFO("basefold_raa_complete_example", "   - Threads: %d\n", config.num_threads);
    
    double prove_start = get_time_ms();
    basefold_raa_proof_t proof = {0};
    int result = basefold_raa_prove(witness, &config, &proof);
    if (result != 0) {
        LOG_ERROR("example", "Proof generation failed");
        return 1;
    }
    
    double prove_time = get_time_ms() - prove_start;
    LOG_INFO("basefold_raa_complete_example", "   - Proof time: %.2f ms\n", prove_time);
    LOG_INFO("basefold_raa_complete_example", "   - Proof size: %zu bytes (%.1f KB)\n", proof.size, proof.size / 1024.0);
    
    // Step 5: Verify proof
    LOG_INFO("basefold_raa_complete_example", "\n5. Verifying proof...\n");
    double verify_start = get_time_ms();
    
    result = basefold_raa_verify(&proof, &config);
    double verify_time = get_time_ms() - verify_start;
    
    if (result == 0) {
        LOG_INFO("basefold_raa_complete_example", "   ✓ Proof verified successfully!\n");
    } else {
        LOG_INFO("basefold_raa_complete_example", "   ✗ Proof verification failed\n");
        return 1;
    }
    LOG_INFO("basefold_raa_complete_example", "   - Verification time: %.2f ms\n", verify_time);
    
    // Step 6: Serialize proof to file
    LOG_INFO("basefold_raa_complete_example", "\n6. Saving proof to file...\n");
    FILE* fp = fopen("example_proof.bfp", "wb");
    if (fp) {
        fwrite(proof.data, 1, proof.size, fp);
        fclose(fp);
        LOG_INFO("basefold_raa_complete_example", "   - Saved to: example_proof.bfp\n");
    }
    
    // Performance summary
    LOG_INFO("basefold_raa_complete_example", "\n=============================\n");
    LOG_INFO("basefold_raa_complete_example", "Performance Summary:\n");
    LOG_INFO("basefold_raa_complete_example", "  - Circuit evaluation: %.2f ms\n", eval_time);
    LOG_INFO("basefold_raa_complete_example", "  - Proof generation: %.2f ms\n", prove_time);
    LOG_INFO("basefold_raa_complete_example", "  - Proof verification: %.2f ms\n", verify_time);
    LOG_INFO("basefold_raa_complete_example", "  - Total time: %.2f ms\n", eval_time + prove_time + verify_time);
    LOG_INFO("basefold_raa_complete_example", "  - Proof size: %.1f KB\n", proof.size / 1024.0);
    
    // Cleanup
    basefold_raa_proof_free(&proof);
    circuit_free(circuit);
    free(witness);
    free(inputs);
    free(input_bytes);
    
    return 0;
}