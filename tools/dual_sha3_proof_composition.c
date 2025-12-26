/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @brief Empirical test for composing two SHA3-256 pre-image proofs
 * 
 * This program:
 * 1. Generates two independent SHA3-256 circuits for different inputs
 * 2. Creates BaseFold RAA proofs for each circuit
 * 3. Composes them into a single proof that verifies both pre-images
 * 4. Analyzes performance metrics and proof sizes
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <unistd.h>
#include <sys/stat.h>
#include "basefold_raa.h"
#include "sha3.h"
#include "circuit_generator.h"
#include "circuit_io.h"
#include "evaluator.h"
#include "logger.h"

#define COMPOSE_DIR "composed_proofs"
#define METRICS_FILE "composed_proofs/metrics.csv"

/* Performance measurement utilities */
static double get_time_ms() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000.0 + tv.tv_usec / 1000.0;
}

/* Composition proof structure */
typedef struct {
    // Individual proofs
    basefold_raa_proof_t proof1;
    basefold_raa_proof_t proof2;
    
    // Composition metadata
    uint8_t hash1[32];  // SHA3-256 output for input1
    uint8_t hash2[32];  // SHA3-256 output for input2
    uint8_t composition_commitment[32];  // Commitment to both proofs
    
    // Performance metrics
    double proof1_gen_time_ms;
    double proof2_gen_time_ms;
    double composition_time_ms;
    double total_time_ms;
    size_t proof1_size;
    size_t proof2_size;
    size_t composed_size;
} composed_proof_t;

/* Generate SHA3-256 circuit for given input */
static circuit_t* generate_sha3_circuit(const char *input, size_t input_len) {
    circuit_t *circuit = circuit_new();
    if (!circuit) return NULL;
    
    // Set up input wires for the message
    size_t num_input_bits = input_len * 8;
    wire_t *input_wires = calloc(num_input_bits, sizeof(wire_t));
    
    // Convert input bytes to bits
    for (size_t i = 0; i < input_len; i++) {
        for (size_t j = 0; j < 8; j++) {
            input_wires[i * 8 + j] = circuit_add_input(circuit);
            // Set the input value
            circuit_set_input_bit(circuit, input_wires[i * 8 + j], 
                                 (input[i] >> j) & 1);
        }
    }
    
    // Generate SHA3-256 circuit
    wire_t *output_wires = calloc(256, sizeof(wire_t));
    generate_sha3_256_circuit(circuit, input_wires, num_input_bits, output_wires);
    
    // Mark outputs
    for (size_t i = 0; i < 256; i++) {
        circuit_mark_output(circuit, output_wires[i]);
    }
    
    free(input_wires);
    free(output_wires);
    
    return circuit;
}

/* Evaluate circuit and create witness */
static gf128_t* evaluate_sha3_circuit(circuit_t *circuit, uint8_t *hash_output) {
    // Evaluate the circuit
    bool *wire_values = circuit_evaluate(circuit);
    if (!wire_values) return NULL;
    
    // Extract hash output
    size_t num_outputs = circuit_get_num_outputs(circuit);
    if (num_outputs != 256) {
        free(wire_values);
        return NULL;
    }
    
    // Convert output bits to bytes
    memset(hash_output, 0, 32);
    wire_t *outputs = circuit_get_outputs(circuit);
    for (size_t i = 0; i < 256; i++) {
        if (wire_values[outputs[i]]) {
            hash_output[i / 8] |= (1 << (i % 8));
        }
    }
    
    // Convert to GF128 witness for BaseFold
    size_t num_gates = circuit_get_num_gates(circuit);
    size_t witness_size = 1ULL << (32 - __builtin_clz(num_gates - 1)); // Next power of 2
    gf128_t *witness = calloc(witness_size, sizeof(gf128_t));
    
    // Encode wire values as GF128 elements
    for (size_t i = 0; i < circuit_get_num_wires(circuit) && i < witness_size; i++) {
        if (wire_values[i]) {
            witness[i] = gf128_one();
        } else {
            witness[i] = gf128_zero();
        }
    }
    
    free(wire_values);
    return witness;
}

/* Compose two proofs into one */
static void compose_proofs(composed_proof_t *composed, 
                          const basefold_raa_proof_t *proof1,
                          const basefold_raa_proof_t *proof2,
                          const uint8_t *hash1, 
                          const uint8_t *hash2) {
    double start_time = get_time_ms();
    
    // Copy individual proofs
    memcpy(&composed->proof1, proof1, sizeof(basefold_raa_proof_t));
    memcpy(&composed->proof2, proof2, sizeof(basefold_raa_proof_t));
    memcpy(composed->hash1, hash1, 32);
    memcpy(composed->hash2, hash2, 32);
    
    // Create composition commitment using SHA3-256
    uint8_t composition_data[128];
    memcpy(composition_data, proof1->proof_tag, 32);
    memcpy(composition_data + 32, proof2->proof_tag, 32);
    memcpy(composition_data + 64, hash1, 32);
    memcpy(composition_data + 96, hash2, 32);
    
    sha3_256(composition_data, 128, composed->composition_commitment);
    
    composed->composition_time_ms = get_time_ms() - start_time;
    composed->composed_size = composed->proof1_size + composed->proof2_size + 96; // Extra metadata
}

/* Verify composed proof */
static bool verify_composed_proof(const composed_proof_t *composed,
                                 const basefold_raa_config_t *config) {
    // Verify composition commitment
    uint8_t expected_commitment[32];
    uint8_t composition_data[128];
    memcpy(composition_data, composed->proof1.proof_tag, 32);
    memcpy(composition_data + 32, composed->proof2.proof_tag, 32);
    memcpy(composition_data + 64, composed->hash1, 32);
    memcpy(composition_data + 96, composed->hash2, 32);
    
    sha3_256(composition_data, 128, expected_commitment);
    
    if (memcmp(expected_commitment, composed->composition_commitment, 32) != 0) {
        printf("Composition commitment verification failed\n");
        return false;
    }
    
    // Verify individual proofs
    if (basefold_raa_verify(&composed->proof1, config) != 0) {
        printf("Proof 1 verification failed\n");
        return false;
    }
    
    if (basefold_raa_verify(&composed->proof2, config) != 0) {
        printf("Proof 2 verification failed\n");
        return false;
    }
    
    return true;
}

/* Save metrics to CSV */
static void save_metrics(const composed_proof_t *composed, const char *input1, const char *input2) {
    FILE *fp = fopen(METRICS_FILE, "a");
    if (!fp) return;
    
    // Add header if file is new
    struct stat st;
    if (stat(METRICS_FILE, &st) == 0 && st.st_size == 0) {
        fprintf(fp, "timestamp,input1_len,input2_len,proof1_gen_ms,proof2_gen_ms,"
                    "composition_ms,total_ms,proof1_size,proof2_size,composed_size,"
                    "size_overhead_pct,time_overhead_pct\n");
    }
    
    double time_overhead = (composed->composition_time_ms / 
                           (composed->proof1_gen_time_ms + composed->proof2_gen_time_ms)) * 100;
    double size_overhead = ((double)(composed->composed_size - composed->proof1_size - composed->proof2_size) /
                           (composed->proof1_size + composed->proof2_size)) * 100;
    
    fprintf(fp, "%ld,%zu,%zu,%.2f,%.2f,%.2f,%.2f,%zu,%zu,%zu,%.2f,%.2f\n",
            time(NULL), strlen(input1), strlen(input2),
            composed->proof1_gen_time_ms, composed->proof2_gen_time_ms,
            composed->composition_time_ms, composed->total_time_ms,
            composed->proof1_size, composed->proof2_size, composed->composed_size,
            size_overhead, time_overhead);
    
    fclose(fp);
}

/* Print detailed analysis */
static void print_analysis(const composed_proof_t *composed, 
                          const char *input1, const char *input2) {
    printf("\n╔══════════════════════════════════════════════════════════════════╗\n");
    printf("║           DUAL SHA3 PROOF COMPOSITION ANALYSIS                   ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    
    // Input details
    printf("║ Input 1: %-55s ║\n", input1);
    printf("║ Hash 1:  ");
    for (int i = 0; i < 32; i++) printf("%02x", composed->hash1[i]);
    printf(" ║\n");
    
    printf("║ Input 2: %-55s ║\n", input2);
    printf("║ Hash 2:  ");
    for (int i = 0; i < 32; i++) printf("%02x", composed->hash2[i]);
    printf(" ║\n");
    
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║                    PERFORMANCE METRICS                           ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    
    // Time metrics
    printf("║ Proof 1 generation:     %7.2f ms                              ║\n", 
           composed->proof1_gen_time_ms);
    printf("║ Proof 2 generation:     %7.2f ms                              ║\n", 
           composed->proof2_gen_time_ms);
    printf("║ Composition overhead:   %7.2f ms                              ║\n", 
           composed->composition_time_ms);
    printf("║ Total time:            %7.2f ms                              ║\n", 
           composed->total_time_ms);
    
    double parallel_speedup = (composed->proof1_gen_time_ms + composed->proof2_gen_time_ms) / 
                              composed->total_time_ms;
    printf("║ Parallel speedup:         %.2fx                                  ║\n", 
           parallel_speedup);
    
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║                      SIZE ANALYSIS                               ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    
    // Size metrics
    printf("║ Proof 1 size:          %7zu bytes                            ║\n", 
           composed->proof1_size);
    printf("║ Proof 2 size:          %7zu bytes                            ║\n", 
           composed->proof2_size);
    printf("║ Composed proof size:   %7zu bytes                            ║\n", 
           composed->composed_size);
    printf("║ Size overhead:         %7zu bytes (%.1f%%)                    ║\n", 
           composed->composed_size - composed->proof1_size - composed->proof2_size,
           ((double)(composed->composed_size - composed->proof1_size - composed->proof2_size) /
            (composed->proof1_size + composed->proof2_size)) * 100);
    
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    printf("║                     EFFICIENCY ANALYSIS                          ║\n");
    printf("╠══════════════════════════════════════════════════════════════════╣\n");
    
    // Efficiency metrics
    double bytes_per_ms = composed->composed_size / composed->total_time_ms;
    double proofs_per_second = 1000.0 / composed->total_time_ms;
    
    printf("║ Throughput:            %.2f KB/s                                ║\n", 
           bytes_per_ms);
    printf("║ Proof rate:            %.2f composed proofs/second              ║\n", 
           proofs_per_second);
    printf("║ Amortized time/proof:  %.2f ms                                  ║\n", 
           composed->total_time_ms / 2);
    printf("║ Amortized size/proof:  %.2f KB                                  ║\n", 
           composed->composed_size / 2048.0);
    
    printf("╚══════════════════════════════════════════════════════════════════╝\n");
}

int main(int argc, char *argv[]) {
    // Default inputs
    const char *input1 = "Hello, World!";
    const char *input2 = "Gate Computer Proof Composition";
    
    // Parse arguments
    if (argc >= 2) input1 = argv[1];
    if (argc >= 3) input2 = argv[2];
    
    // Create output directory
    mkdir(COMPOSE_DIR, 0755);
    
    printf("=== Dual SHA3 Proof Composition Test ===\n");
    printf("Input 1: %s (length: %zu)\n", input1, strlen(input1));
    printf("Input 2: %s (length: %zu)\n", input2, strlen(input2));
    
    composed_proof_t composed = {0};
    double total_start = get_time_ms();
    
    // Step 1: Generate SHA3 circuits
    printf("\n[1/6] Generating SHA3 circuits...\n");
    circuit_t *circuit1 = generate_sha3_circuit(input1, strlen(input1));
    circuit_t *circuit2 = generate_sha3_circuit(input2, strlen(input2));
    
    if (!circuit1 || !circuit2) {
        fprintf(stderr, "Failed to generate circuits\n");
        return 1;
    }
    
    printf("  Circuit 1: %zu gates\n", circuit_get_num_gates(circuit1));
    printf("  Circuit 2: %zu gates\n", circuit_get_num_gates(circuit2));
    
    // Step 2: Evaluate circuits to get witnesses and hashes
    printf("\n[2/6] Evaluating circuits...\n");
    gf128_t *witness1 = evaluate_sha3_circuit(circuit1, composed.hash1);
    gf128_t *witness2 = evaluate_sha3_circuit(circuit2, composed.hash2);
    
    if (!witness1 || !witness2) {
        fprintf(stderr, "Failed to evaluate circuits\n");
        return 1;
    }
    
    // Step 3: Configure BaseFold RAA
    printf("\n[3/6] Configuring BaseFold RAA...\n");
    basefold_raa_config_t config = {
        .num_variables = 18,  // 2^18 = 262K gates (enough for SHA3)
        .security_level = 122,
        .enable_zk = 1,
        .num_threads = 4
    };
    
    size_t witness_size = 1ULL << config.num_variables;
    
    // Step 4: Generate proof 1
    printf("\n[4/6] Generating proof 1...\n");
    double proof1_start = get_time_ms();
    basefold_raa_proof_t proof1 = {0};
    
    if (basefold_raa_prove(witness1, &config, &proof1) != 0) {
        fprintf(stderr, "Failed to generate proof 1\n");
        return 1;
    }
    
    composed.proof1_gen_time_ms = get_time_ms() - proof1_start;
    composed.proof1_size = basefold_raa_proof_size(&proof1);
    printf("  Generated in %.2f ms, size: %zu bytes\n", 
           composed.proof1_gen_time_ms, composed.proof1_size);
    
    // Step 5: Generate proof 2
    printf("\n[5/6] Generating proof 2...\n");
    double proof2_start = get_time_ms();
    basefold_raa_proof_t proof2 = {0};
    
    if (basefold_raa_prove(witness2, &config, &proof2) != 0) {
        fprintf(stderr, "Failed to generate proof 2\n");
        return 1;
    }
    
    composed.proof2_gen_time_ms = get_time_ms() - proof2_start;
    composed.proof2_size = basefold_raa_proof_size(&proof2);
    printf("  Generated in %.2f ms, size: %zu bytes\n", 
           composed.proof2_gen_time_ms, composed.proof2_size);
    
    // Step 6: Compose proofs
    printf("\n[6/6] Composing proofs...\n");
    compose_proofs(&composed, &proof1, &proof2, composed.hash1, composed.hash2);
    composed.total_time_ms = get_time_ms() - total_start;
    
    printf("  Composition completed in %.2f ms\n", composed.composition_time_ms);
    printf("  Total time: %.2f ms\n", composed.total_time_ms);
    
    // Verify composed proof
    printf("\nVerifying composed proof...\n");
    double verify_start = get_time_ms();
    bool valid = verify_composed_proof(&composed, &config);
    double verify_time = get_time_ms() - verify_start;
    
    if (valid) {
        printf("✓ Composed proof verified successfully in %.2f ms\n", verify_time);
    } else {
        printf("✗ Composed proof verification failed\n");
        return 1;
    }
    
    // Print analysis
    print_analysis(&composed, input1, input2);
    
    // Save metrics
    save_metrics(&composed, input1, input2);
    printf("\nMetrics saved to: %s\n", METRICS_FILE);
    
    // Cleanup
    circuit_free(circuit1);
    circuit_free(circuit2);
    free(witness1);
    free(witness2);
    basefold_raa_proof_free(&proof1);
    basefold_raa_proof_free(&proof2);
    
    return 0;
}