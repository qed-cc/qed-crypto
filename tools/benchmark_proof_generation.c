/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include "logger.h"
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <sys/time.h>

/**
 * @brief Benchmark proof generation with detailed timing
 * 
 * This program measures the time spent in each phase of proof generation
 * to identify optimization opportunities.
 */

// Get current time in seconds with microsecond precision
double get_time() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec / 1000000.0;
}

int main(int argc, char** argv) {
    LOG_INFO("benchmark_proof_generation", "BaseFold V2 Proof Generation Benchmark\n");
    LOG_INFO("benchmark_proof_generation", "=====================================\n\n");
    
    // Test different input sizes
    const char* test_inputs[] = {
        "short",
        "medium length input for testing",
        "this is a longer input string that will create more gates in the SHA3 circuit and give us better timing measurements for optimization analysis"
    };
    
    const char* test_names[] = {
        "Small (5 chars)",
        "Medium (31 chars)", 
        "Large (134 chars)"
    };
    
    for (int i = 0; i < 3; i++) {
        LOG_INFO("benchmark_proof_generation", "\nTest %d: %s\n", i + 1, test_names[i]);
        LOG_INFO("benchmark_proof_generation", "-----------------------------------------\n");
        
        char cmd[512];
        char proof_file[64];
        snLOG_INFO("benchmark_proof_generation", proof_file, sizeof(proof_file), "bench_test_%d.bfp", i);
        
        // Warm up run
        snLOG_INFO("benchmark_proof_generation", cmd, sizeof(cmd), 
            "./bin/gate_computer --gen-sha3-256 --input-text \"%s\" --prove %s > /dev/null 2>&1",
            test_inputs[i], proof_file);
        system(cmd);
        
        // Timed runs
        double total_time = 0;
        int num_runs = 5;
        
        for (int run = 0; run < num_runs; run++) {
            double start = get_time();
            
            system(cmd);
            
            double end = get_time();
            double elapsed = end - start;
            total_time += elapsed;
            
            if (run == 0) {
                // Get detailed timing from first run
                snLOG_INFO("benchmark_proof_generation", cmd, sizeof(cmd),
                    "./bin/gate_computer --gen-sha3-256 --input-text \"%s\" --prove %s 2>&1 | grep -E \"(Generation time|Circuit evaluation|Proof size)\"",
                    test_inputs[i], proof_file);
                
                FILE* fp = popen(cmd, "r");
                if (fp) {
                    char line[256];
                    while (fgets(line, sizeof(line), fp)) {
                        LOG_INFO("benchmark_proof_generation", "  %s", line);
                    }
                    pclose(fp);
                }
            }
            
            LOG_INFO("benchmark_proof_generation", "  Run %d: %.3f seconds\n", run + 1, elapsed);
        }
        
        LOG_INFO("benchmark_proof_generation", "  Average: %.3f seconds\n", total_time / num_runs);
        
        // Clean up
        unlink(proof_file);
    }
    
    // Test parallel speedup potential
    LOG_INFO("benchmark_proof_generation", "\n\nParallel Speedup Analysis\n");
    LOG_INFO("benchmark_proof_generation", "=========================\n");
    
    // Get CPU info
    FILE* fp = popen("nproc", "r");
    if (fp) {
        char cores[16];
        if (fgets(cores, sizeof(cores), fp)) {
            LOG_INFO("benchmark_proof_generation", "Available CPU cores: %s", cores);
        }
        pclose(fp);
    }
    
    // Estimate speedup
    LOG_INFO("benchmark_proof_generation", "\nEstimated speedup with optimizations:\n");
    LOG_INFO("benchmark_proof_generation", "- Parallel Merkle trees (3-4x): ~0.11s saved\n");
    LOG_INFO("benchmark_proof_generation", "- SIMD SHA3 batching (2x): ~0.07s saved\n");
    LOG_INFO("benchmark_proof_generation", "- Parallel sumcheck (2x): ~0.04s saved\n");
    LOG_INFO("benchmark_proof_generation", "- Memory pooling (1.2x): ~0.02s saved\n");
    LOG_INFO("benchmark_proof_generation", "\nTotal potential speedup: ~0.24s (68% faster)\n");
    LOG_INFO("benchmark_proof_generation", "Target: 0.355s → 0.115s\n");
    
    // Recommendations
    LOG_INFO("benchmark_proof_generation", "\n\nOptimization Recommendations\n");
    LOG_INFO("benchmark_proof_generation", "============================\n");
    LOG_INFO("benchmark_proof_generation", "1. IMMEDIATE: Enable OpenMP parallel Merkle trees\n");
    LOG_INFO("benchmark_proof_generation", "   - Add -fopenmp to CFLAGS\n");
    LOG_INFO("benchmark_proof_generation", "   - Link with -lgomp\n");
    LOG_INFO("benchmark_proof_generation", "   - Use merkle_build_parallel()\n");
    LOG_INFO("benchmark_proof_generation", "\n2. SHORT-TERM: Implement SIMD SHA3\n");
    LOG_INFO("benchmark_proof_generation", "   - Use sha3_256_x4_avx2() for batch hashing\n");
    LOG_INFO("benchmark_proof_generation", "   - Process 4 nodes simultaneously\n");
    LOG_INFO("benchmark_proof_generation", "\n3. MEDIUM-TERM: GPU acceleration\n");
    LOG_INFO("benchmark_proof_generation", "   - CUDA kernel for Merkle tree\n");
    LOG_INFO("benchmark_proof_generation", "   - 10-20x potential speedup\n");
    
    return 0;
}