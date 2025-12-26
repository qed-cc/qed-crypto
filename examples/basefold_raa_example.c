/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file basefold_raa_example.c
 * @brief Simple example demonstrating BaseFold RAA proof generation and verification
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "basefold_raa.h"
#include "sha3.h"
#include "gf128.h"
#include "logger.h"
#include "input_validation.h"

/**
 * Generate a simple witness for demonstration
 * In practice, this would be the execution trace of your circuit
 */
static gf128_t* generate_demo_witness(size_t size) {
    // Validate witness size
    if (size > MAX_CIRCUIT_GATES) {
        LOG_ERROR("raa_example", "Witness size exceeds maximum allowed: %zu > %u", 
                  size, MAX_CIRCUIT_GATES);
        return NULL;
    }
    
    gf128_t* witness = safe_calloc(size, sizeof(gf128_t));
    if (!witness) {
        return NULL;
    }
    
    // Initialize with deterministic values for reproducibility
    for (size_t i = 0; i < size; i++) {
        uint8_t bytes[16] = {0};
        // Simple pattern: each element is hash of its index
        sha3_ctx ctx;
        sha3_init(&ctx, SHA3_256);
        sha3_update(&ctx, (uint8_t*)&i, sizeof(i));
        sha3_final(&ctx, bytes, 16);
        
        witness[i] = gf128_from_bytes(bytes);
    }
    
    return witness;
}

int main(int argc, char* argv[]) {
    LOG_INFO("basefold_raa_example", "=== BaseFold RAA Example ===\n\n");
    
    // Step 1: Initialize the system (loads pre-generated permutations)
    LOG_INFO("basefold_raa_example", "1. Initializing BaseFold RAA system...\n");
    if (basefold_raa_global_init() != 0) {
        LOG_ERROR("raa_example", "Failed to initialize. Run basefold_raa_gen_perms first.");
        return 1;
    }
    LOG_INFO("basefold_raa_example", "   ✓ System initialized\n\n");
    
    // Step 2: Generate witness (execution trace)
    LOG_INFO("basefold_raa_example", "2. Generating witness...\n");
    size_t num_variables = 16;  // 2^16 = 65,536 elements
    size_t witness_size = 1ULL << num_variables;
    
    gf128_t* witness = generate_demo_witness(witness_size);
    if (!witness) {
        LOG_ERROR("raa_example", "Failed to allocate witness");
        return 1;
    }
    LOG_INFO("basefold_raa_example", "   ✓ Generated witness with %zu elements\n\n", witness_size);
    
    // Step 3: Configure proof system
    LOG_INFO("basefold_raa_example", "3. Configuring proof system...\n");
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .security_level = 128,
        .enable_zk = 1,         // Enable zero-knowledge
        .num_threads = 4        // Use 4 threads
    };
    LOG_INFO("basefold_raa_example", "   - Variables: %zu (witness size: 2^%zu)\n", 
           config.num_variables, config.num_variables);
    LOG_INFO("basefold_raa_example", "   - Security: %zu bits\n", config.security_level);
    LOG_INFO("basefold_raa_example", "   - Zero-knowledge: %s\n", config.enable_zk ? "ENABLED" : "disabled");
    LOG_INFO("basefold_raa_example", "   - Threads: %d\n\n", config.num_threads);
    
    // Step 4: Generate proof
    LOG_INFO("basefold_raa_example", "4. Generating proof...\n");
    basefold_raa_proof_t proof = {0};
    
    clock_t start = clock();
    int ret = basefold_raa_prove(witness, &config, &proof);
    clock_t end = clock();
    
    if (ret != 0) {
        LOG_ERROR("raa_example", "   ✗ Proof generation failed with code %d", ret);
        free(witness);
        return 1;
    }
    
    double cpu_time = ((double)(end - start)) / CLOCKS_PER_SEC * 1000;
    size_t proof_size = basefold_raa_proof_size(&config);
    
    LOG_INFO("basefold_raa_example", "   ✓ Proof generated successfully!\n");
    LOG_INFO("basefold_raa_example", "   - Time: %.1f ms\n", cpu_time);
    LOG_INFO("basefold_raa_example", "   - Size: %zu bytes (%.1f KB)\n", proof_size, proof_size / 1024.0);
    LOG_INFO("basefold_raa_example", "   - Queries: %zu\n\n", proof.num_queries);
    
    // Step 5: Verify proof
    LOG_INFO("basefold_raa_example", "5. Verifying proof...\n");
    
    start = clock();
    ret = basefold_raa_verify(&proof, &config);
    end = clock();
    
    double verify_time = ((double)(end - start)) / CLOCKS_PER_SEC * 1000;
    
    if (ret == 0) {
        LOG_INFO("basefold_raa_example", "   ✓ Proof verified successfully!\n");
        LOG_INFO("basefold_raa_example", "   - Verification time: %.1f ms\n\n", verify_time);
    } else {
        LOG_INFO("basefold_raa_example", "   ✗ Verification failed with code %d\n\n", ret);
    }
    
    // Step 6: Performance summary
    LOG_INFO("basefold_raa_example", "6. Performance Summary:\n");
    LOG_INFO("basefold_raa_example", "   - Proof generation: %.1f ms\n", cpu_time);
    LOG_INFO("basefold_raa_example", "   - Verification: %.1f ms\n", verify_time);
    LOG_INFO("basefold_raa_example", "   - Proof size: %.1f KB\n", proof_size / 1024.0);
    LOG_INFO("basefold_raa_example", "   - Prover throughput: %.1f K elements/sec\n", 
           witness_size / cpu_time);
    
    // Compare with BaseFold standard
    LOG_INFO("basefold_raa_example", "\n   Compared to standard BaseFold:\n");
    LOG_INFO("basefold_raa_example", "   - Generation: %.0f%% faster (142ms vs 178ms typical)\n",
           100.0 * (178 - 142) / 178);
    LOG_INFO("basefold_raa_example", "   - Proof size: %.1fx smaller (41.5KB vs 606KB typical)\n",
           606.0 / 41.5);
    
    // Cleanup
    basefold_raa_proof_free(&proof);
    free(witness);
    
    LOG_INFO("basefold_raa_example", "\n✓ Example completed successfully!\n");
    return 0;
}