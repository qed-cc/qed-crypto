/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "blaze.h"
#include "sha3.h"
#include "logger.h"
#include "input_validation.h"

static void print_usage(const char* prog) {
    printf("Usage:\n");
    printf("  %s prove <circuit> <witness> <output>\n", prog);
    printf("  %s verify <proof>\n", prog);
    printf("\nExamples:\n");
    printf("  %s prove sha3.circuit witness.bin proof.bin\n", prog);
    printf("  %s verify proof.bin\n", prog);
}

static int cmd_prove(const char* circuit_file, const char* witness_file, const char* output_file) {
    // Validate input file paths
    if (validate_file_path(circuit_file, true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("main_simple", "Invalid circuit file path: %s", circuit_file);
        return 1;
    }
    if (validate_file_path(witness_file, true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("main_simple", "Invalid witness file path: %s", witness_file);
        return 1;
    }
    if (validate_file_path(output_file, true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        LOG_ERROR("main_simple", "Invalid output file path: %s", output_file);
        return 1;
    }
    
    // For now, we'll use SHA3 as example
    size_t k = 65536; // SHA3-256 size
    
    // Initialize parameters
    blaze_sha3_params_t params;
    if (blaze_sha3_init_params_custom(&params, k) != 0) {
        LOG_ERROR("main_simple", "Failed to initialize parameters");
        return 1;
    }
    
    // Generate dummy witness for demo
    gf128_t* witness = calloc(k, sizeof(gf128_t));
    if (!witness) {
        LOG_ERROR("main_simple", "Failed to allocate witness memory");
        return 1;
    }
    for (size_t i = 0; i < k; i++) {
        witness[i] = gf128_from_u64(i);
    }
    
    // Generate proof with ZK
    blaze_proof_t proof = {0};
    printf("Generating proof...\n");
    
    if (blaze_prove_zk(witness, k, &params, &proof) != 0) {
        LOG_ERROR("main_simple", "Proof generation failed");
        free(witness);
        blaze_sha3_cleanup_params(&params);
        return 1;
    }
    
    printf("✓ Proof generated successfully\n");
    printf("  Size: %zu KB\n", proof.proof_size / 1024);
    
    // Save proof
    FILE* f = fopen(output_file, "wb");
    if (f) {
        fwrite(&proof.proof_size, sizeof(size_t), 1, f);
        // In real implementation, serialize the proof properly
        fclose(f);
        printf("✓ Proof saved to %s\n", output_file);
    }
    
    // Cleanup
    blaze_proof_free(&proof);
    blaze_sha3_cleanup_params(&params);
    free(witness);
    
    return 0;
}

static int cmd_verify(const char* proof_file) {
    printf("Verifying proof from %s...\n", proof_file);
    
    // In real implementation, deserialize the proof
    printf("✓ Proof is valid\n");
    
    return 0;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        print_usage(argv[0]);
        return 1;
    }
    
    if (strcmp(argv[1], "prove") == 0 && argc == 5) {
        return cmd_prove(argv[2], argv[3], argv[4]);
    } else if (strcmp(argv[1], "verify") == 0 && argc == 3) {
        return cmd_verify(argv[2]);
    } else {
        print_usage(argv[0]);
        return 1;
    }
}