/**
 * @file benchmark_sumcheck.c
 * @brief Focused benchmark for sumcheck performance
 * 
 * Measures the performance of the sumcheck algorithm at different sizes
 * to establish a baseline and track improvements.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include "gate_sumcheck_multilinear.h"
#include "gf128.h"
#include "transcript.h"

// Initialize evaluation buffer with random values
static void init_eval_buffer(gf128_t* buffer, size_t size) {
    for (size_t i = 0; i < size; i++) {
        buffer[i] = gf128_rand();
    }
}

// Create a simple circuit trace for benchmarking
static void create_trace_data(
    gf128_t* left_wire, 
    gf128_t* right_wire, 
    gf128_t* output_wire,
    uint8_t* selector,
    size_t num_gates)
{
    for (size_t i = 0; i < num_gates; i++) {
        left_wire[i] = gf128_rand();
        right_wire[i] = gf128_rand();
        
        // Mix of XOR and AND gates
        selector[i] = (i % 3) != 0 ? 0 : 1;  // 2/3 XOR, 1/3 AND
        
        if (selector[i] == 0) {
            // XOR gate
            output_wire[i] = gf128_add(left_wire[i], right_wire[i]);
        } else {
            // AND gate
            output_wire[i] = gf128_mul(left_wire[i], right_wire[i]);
        }
    }
}

// Benchmark sumcheck at a specific size
static double benchmark_size(size_t num_gates) {
    // Calculate number of variables
    size_t num_vars = 0;
    size_t temp = num_gates - 1;
    while (temp > 0) {
        num_vars++;
        temp >>= 1;
    }
    
    // Ensure we have exact power of 2
    size_t padded_size = 1ULL << num_vars;
    assert(padded_size == num_gates);
    
    // Allocate trace data
    gf128_t* left_wire = calloc(num_gates, sizeof(gf128_t));
    gf128_t* right_wire = calloc(num_gates, sizeof(gf128_t));
    gf128_t* output_wire = calloc(num_gates, sizeof(gf128_t));
    uint8_t* selector = calloc(num_gates, sizeof(uint8_t));
    
    // Create synthetic trace
    create_trace_data(left_wire, right_wire, output_wire, selector, num_gates);
    
    // Initialize sumcheck instance
    gate_sumcheck_ml_t instance;
    memset(&instance, 0, sizeof(instance));
    
    instance.num_vars = num_vars;
    instance.W_L = left_wire;
    instance.W_R = right_wire;
    instance.W_O = output_wire;
    instance.S = selector;
    instance.num_trace_gates = num_gates;
    
    // Create transcript for Fiat-Shamir
    transcript_t transcript;
    transcript_init(&transcript, "sumcheck_benchmark");
    
    // Time the sumcheck protocol
    clock_t start = clock();
    
    // Run gate sumcheck
    gf128_t claimed_sum = gf128_zero();
    gf128_t* challenges = calloc(num_vars, sizeof(gf128_t));
    
    gate_sumcheck_ml_prove(&instance, &transcript, claimed_sum, challenges);
    
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    
    // Cleanup
    free(left_wire);
    free(right_wire);
    free(output_wire);
    free(selector);
    free(challenges);
    
    return elapsed;
}

int main() {
    printf("=== SumCheck Performance Benchmark ===\n");
    printf("Current implementation baseline\n\n");
    
    // Test sizes from 2^10 to 2^20
    size_t sizes[] = {
        1024,      // 2^10
        4096,      // 2^12
        16384,     // 2^14
        65536,     // 2^16
        262144,    // 2^18 (SHA3-256 size)
        1048576    // 2^20
    };
    
    printf("%-12s %-10s %-15s %-15s %-20s\n", 
           "Gates", "Variables", "Time (s)", "Gates/sec", "MB/s (est)");
    printf("%-12s %-10s %-15s %-15s %-20s\n",
           "-----", "---------", "--------", "---------", "---------");
    
    for (size_t i = 0; i < sizeof(sizes)/sizeof(sizes[0]); i++) {
        size_t num_gates = sizes[i];
        
        // Skip very large sizes if they take too long
        if (num_gates > 262144) {
            printf("%-12zu (skipped - too large for quick test)\n", num_gates);
            continue;
        }
        
        // Warm up
        benchmark_size(num_gates);
        
        // Run multiple times and take average
        double total_time = 0;
        int runs = (num_gates <= 16384) ? 5 : 3;
        
        for (int r = 0; r < runs; r++) {
            total_time += benchmark_size(num_gates);
        }
        
        double avg_time = total_time / runs;
        double gates_per_sec = num_gates / avg_time;
        
        // Estimate memory bandwidth (4 GF128 elements per gate * 16 bytes each)
        double mb_processed = (num_gates * 4 * 16) / (1024.0 * 1024.0);
        double mb_per_sec = mb_processed / avg_time;
        
        // Calculate number of variables
        size_t num_vars = 0;
        size_t temp = num_gates - 1;
        while (temp > 0) {
            num_vars++;
            temp >>= 1;
        }
        
        printf("%-12zu %-10zu %-15.6f %-15.0f %-20.1f\n",
               num_gates, num_vars, avg_time, gates_per_sec, mb_per_sec);
    }
    
    printf("\nNotes:\n");
    printf("- SHA3-256 uses 262,144 gates (2^18)\n");
    printf("- Memory bandwidth estimate assumes 4 GF128 elements per gate\n");
    printf("- Each GF128 element is 16 bytes\n");
    
    // Print system info if available
    #ifdef __x86_64__
    printf("\nCPU Features:\n");
    printf("- AVX2: %s\n", __builtin_cpu_supports("avx2") ? "Yes" : "No");
    printf("- AVX-512F: %s\n", __builtin_cpu_supports("avx512f") ? "Yes" : "No");
    #endif
    
    return 0;
}