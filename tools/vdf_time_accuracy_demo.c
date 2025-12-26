/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include "../modules/sha3/include/sha3.h"

/* VDF Time Accuracy Demonstration
 * 
 * This demo shows the challenges of mapping CPU iterations to wall-clock time
 * and demonstrates practical approaches to time guarantees.
 */

// Hardware performance assumptions (SHA3-256 operations per second)
#define SHA3_RATE_SMARTPHONE      50000ULL        // 50K/sec
#define SHA3_RATE_LAPTOP         100000ULL        // 100K/sec
#define SHA3_RATE_DESKTOP        125000ULL        // 125K/sec
#define SHA3_RATE_SERVER         500000ULL        // 500K/sec
#define SHA3_RATE_GPU           5000000ULL        // 5M/sec
#define SHA3_RATE_FPGA         40000000ULL        // 40M/sec
#define SHA3_RATE_ASIC_2024   200000000ULL        // 200M/sec
#define SHA3_RATE_ASIC_2030  1000000000ULL        // 1B/sec (projected)
#define SHA3_RATE_THEORETICAL 5000000000ULL        // 5B/sec (physical limit?)

// Time constants
#define SECONDS_PER_HOUR     3600ULL
#define SECONDS_PER_DAY      86400ULL
#define SECONDS_PER_YEAR     31536000ULL
#define SECONDS_PER_4_YEARS  126144000ULL

// Benchmark actual SHA3 performance
static double benchmark_sha3_rate(void) {
    uint8_t state[32] = {0};
    const int iterations = 100000;
    
    clock_t start = clock();
    
    for (int i = 0; i < iterations; i++) {
        sha3_256(state, state, 32);
    }
    
    clock_t end = clock();
    double seconds = (double)(end - start) / CLOCKS_PER_SEC;
    
    return iterations / seconds;
}

// Calculate iterations needed for target time
static uint64_t calculate_iterations(uint64_t target_seconds, uint64_t hash_rate) {
    return target_seconds * hash_rate;
}

// Calculate time for given iterations on different hardware
static void analyze_computation_time(uint64_t iterations) {
    printf("\nTime to compute %llu iterations on different hardware:\n", iterations);
    printf("════════════════════════════════════════════════════════════════\n");
    
    struct {
        const char* name;
        uint64_t rate;
        const char* description;
    } hardware[] = {
        {"Smartphone",    SHA3_RATE_SMARTPHONE,  "ARM Cortex-A55"},
        {"Laptop",        SHA3_RATE_LAPTOP,      "Intel Core i5"},
        {"Desktop",       SHA3_RATE_DESKTOP,     "Intel Core i9"},
        {"Server",        SHA3_RATE_SERVER,      "Intel Xeon"},
        {"GPU",           SHA3_RATE_GPU,         "NVIDIA RTX 4090"},
        {"FPGA",          SHA3_RATE_FPGA,        "Xilinx Virtex"},
        {"ASIC 2024",     SHA3_RATE_ASIC_2024,   "Custom SHA3 chip"},
        {"ASIC 2030",     SHA3_RATE_ASIC_2030,   "Future projection"},
        {"Theoretical",   SHA3_RATE_THEORETICAL, "Physical limit?"}
    };
    
    for (int i = 0; i < sizeof(hardware)/sizeof(hardware[0]); i++) {
        double seconds = (double)iterations / hardware[i].rate;
        
        printf("%-15s (%s):\n", hardware[i].name, hardware[i].description);
        printf("  Rate: %llu SHA3/sec\n", hardware[i].rate);
        printf("  Time: ", hardware[i].name);
        
        if (seconds < 60) {
            printf("%.1f seconds\n", seconds);
        } else if (seconds < 3600) {
            printf("%.1f minutes\n", seconds / 60);
        } else if (seconds < 86400) {
            printf("%.1f hours\n", seconds / 3600);
        } else if (seconds < 31536000) {
            printf("%.1f days\n", seconds / 86400);
        } else {
            printf("%.1f years\n", seconds / 31536000);
        }
        
        // Show speed ratio vs ASIC
        double ratio = (double)SHA3_RATE_ASIC_2024 / hardware[i].rate;
        if (ratio > 1) {
            printf("  Speed: %.1fx slower than 2024 ASIC\n", ratio);
        } else {
            printf("  Speed: %.1fx faster than 2024 ASIC\n", 1/ratio);
        }
        printf("\n");
    }
}

// Show VDF security parameters
static void show_vdf_security_params(void) {
    printf("\n=== VDF Security Parameters ===\n\n");
    
    printf("For claiming \"4 years of computation\":\n");
    printf("─────────────────────────────────────\n");
    
    // Conservative approach
    uint64_t iter_conservative = calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_ASIC_2030);
    printf("CONSERVATIVE (assume future ASIC):\n");
    printf("  Iterations: %llu (%.2e)\n", iter_conservative, (double)iter_conservative);
    printf("  Assumes: 1B SHA3/sec (2030 ASIC)\n");
    printf("  Security: High - resistant to future hardware\n");
    printf("\n");
    
    // Realistic approach
    uint64_t iter_realistic = calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_ASIC_2024);
    printf("REALISTIC (current best ASIC):\n");
    printf("  Iterations: %llu (%.2e)\n", iter_realistic, (double)iter_realistic);
    printf("  Assumes: 200M SHA3/sec (2024 ASIC)\n");
    printf("  Security: Medium - assumes current technology\n");
    printf("\n");
    
    // Risky approach
    uint64_t iter_risky = calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_GPU);
    printf("RISKY (assume only GPU attackers):\n");
    printf("  Iterations: %llu (%.2e)\n", iter_risky, (double)iter_risky);
    printf("  Assumes: 5M SHA3/sec (GPU)\n");
    printf("  Security: Low - vulnerable to ASIC attacks\n");
}

// Demonstrate time bounds calculation
static void demonstrate_time_bounds(void) {
    printf("\n=== Time Bounds for Different Iteration Counts ===\n\n");
    
    uint64_t test_iterations[] = {
        1000000ULL,           // 1 million
        1000000000ULL,        // 1 billion  
        1000000000000ULL,     // 1 trillion
        1000000000000000ULL,  // 1 quadrillion
        calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_ASIC_2024)  // 4 years
    };
    
    const char* labels[] = {
        "1 million iterations",
        "1 billion iterations",
        "1 trillion iterations",
        "1 quadrillion iterations",
        "4-year proof iterations"
    };
    
    for (int i = 0; i < sizeof(test_iterations)/sizeof(test_iterations[0]); i++) {
        uint64_t iter = test_iterations[i];
        
        printf("%s (%.2e):\n", labels[i], (double)iter);
        printf("─────────────────────────────────────────\n");
        
        // Calculate bounds
        double min_time = (double)iter / SHA3_RATE_THEORETICAL;
        double likely_time = (double)iter / SHA3_RATE_ASIC_2024;
        double max_time = (double)iter / SHA3_RATE_SMARTPHONE;
        
        printf("  Minimum time (theoretical limit): ");
        if (min_time < 1) printf("%.3f seconds\n", min_time);
        else if (min_time < 3600) printf("%.1f minutes\n", min_time / 60);
        else if (min_time < 86400) printf("%.1f hours\n", min_time / 3600);
        else if (min_time < 31536000) printf("%.1f days\n", min_time / 86400);
        else printf("%.2f years\n", min_time / 31536000);
        
        printf("  Likely time (2024 ASIC): ");
        if (likely_time < 3600) printf("%.1f minutes\n", likely_time / 60);
        else if (likely_time < 86400) printf("%.1f hours\n", likely_time / 3600);
        else if (likely_time < 31536000) printf("%.1f days\n", likely_time / 86400);
        else printf("%.2f years\n", likely_time / 31536000);
        
        printf("  Maximum time (smartphone): ");
        if (max_time < 86400) printf("%.1f hours\n", max_time / 3600);
        else if (max_time < 31536000) printf("%.1f days\n", max_time / 86400);
        else printf("%.2f years\n", max_time / 31536000);
        
        printf("  Uncertainty factor: %.1fx\n\n", max_time / min_time);
    }
}

// Show practical VDF implementation
static void show_practical_vdf(void) {
    printf("\n=== Practical VDF Implementation ===\n\n");
    
    printf("```c\n");
    printf("// VDF with explicit time bounds\n");
    printf("typedef struct {\n");
    printf("    uint64_t iterations;\n");
    printf("    uint64_t min_seconds;      // Best hardware\n");
    printf("    uint64_t likely_seconds;   // Expected case\n");
    printf("    uint64_t max_seconds;      // Worst hardware\n");
    printf("    char assumptions[256];     // Hardware assumptions\n");
    printf("} vdf_time_proof_t;\n\n");
    
    printf("// Generate proof with confidence interval\n");
    printf("vdf_time_proof_t* generate_4_year_proof(void) {\n");
    printf("    // Use conservative iteration count\n");
    printf("    uint64_t iterations = %llu;\n", 
           calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_ASIC_2030));
    printf("    \n");
    printf("    // Compute VDF (this takes 4+ years)\n");
    printf("    uint8_t result[32];\n");
    printf("    compute_vdf(genesis, result, iterations);\n");
    printf("    \n");
    printf("    // Create proof with time bounds\n");
    printf("    vdf_time_proof_t* proof = malloc(sizeof(vdf_time_proof_t));\n");
    printf("    proof->iterations = iterations;\n");
    printf("    proof->min_seconds = iterations / %llu;  // Future ASIC\n", SHA3_RATE_ASIC_2030);
    printf("    proof->likely_seconds = iterations / %llu;  // Current ASIC\n", SHA3_RATE_ASIC_2024);
    printf("    proof->max_seconds = iterations / %llu;  // Consumer CPU\n", SHA3_RATE_LAPTOP);
    printf("    \n");
    printf("    snprintf(proof->assumptions, 256,\n");
    printf("        \"Min: 2030 ASIC (1B SHA3/s), \"\n");
    printf("        \"Likely: 2024 ASIC (200M SHA3/s), \"\n");
    printf("        \"Max: Consumer CPU (100K SHA3/s)\");\n");
    printf("    \n");
    printf("    return proof;\n");
    printf("}\n");
    printf("```\n");
}

// Main demonstration
int main(void) {
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║             VDF TIME ACCURACY DEMONSTRATION                    ║\n");
    printf("║        CPU-to-Time Mapping Challenges & Solutions              ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    
    // Benchmark local performance
    printf("\n=== Local SHA3 Performance ===\n");
    double local_rate = benchmark_sha3_rate();
    printf("This CPU: %.0f SHA3/sec\n", local_rate);
    printf("Category: ");
    
    if (local_rate < SHA3_RATE_SMARTPHONE) {
        printf("Slower than smartphone (very slow)\n");
    } else if (local_rate < SHA3_RATE_LAPTOP) {
        printf("Smartphone-class\n");
    } else if (local_rate < SHA3_RATE_DESKTOP) {
        printf("Laptop-class\n");
    } else if (local_rate < SHA3_RATE_SERVER) {
        printf("Desktop-class\n");
    } else if (local_rate < SHA3_RATE_GPU) {
        printf("Server-class\n");
    } else {
        printf("GPU-class or better (very fast)\n");
    }
    
    // Analyze 4-year computation
    uint64_t iter_4_years = calculate_iterations(SECONDS_PER_4_YEARS, SHA3_RATE_ASIC_2024);
    printf("\n=== \"4 Years of Computation\" Analysis ===\n");
    printf("Target: Prove at least 4 years have elapsed\n");
    printf("Iterations (assuming 2024 ASIC): %llu (%.2e)\n", iter_4_years, (double)iter_4_years);
    
    analyze_computation_time(iter_4_years);
    show_vdf_security_params();
    demonstrate_time_bounds();
    show_practical_vdf();
    
    printf("\n=== Key Insights ===\n\n");
    printf("1. HARDWARE VARIATION: 100,000x difference between phone and ASIC\n");
    printf("2. TIME UNCERTAINTY: \"4 years\" could mean 4-50,000 years depending on hardware\n");
    printf("3. SECURITY REQUIREMENT: Must assume attacker has best possible hardware\n");
    printf("4. FUTURE PROOFING: Account for Moore's Law improvements\n");
    printf("5. PRACTICAL APPROACH: State confidence intervals, not exact times\n");
    
    printf("\n=== Recommendations ===\n\n");
    printf("✓ Use VDFs for RELATIVE time ordering (A before B)\n");
    printf("✓ Use VDFs for MINIMUM age proofs (at least X old)\n");
    printf("✗ Don't claim exact wall-clock times\n");
    printf("✗ Don't assume consumer hardware performance\n");
    printf("✓ Always state hardware assumptions explicitly\n");
    printf("✓ Include confidence intervals in time claims\n");
    printf("✓ Plan for regular difficulty adjustments\n");
    
    printf("\n");
    return 0;
}