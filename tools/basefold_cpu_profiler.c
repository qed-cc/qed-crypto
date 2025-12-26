/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <immintrin.h>
#include <x86intrin.h>
#include "sha3.h"
#include "gf128.h"

// CPU cycle counting
static inline uint64_t rdtsc() {
    unsigned int lo, hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

// Profile structure
typedef struct {
    const char* name;
    uint64_t cycles;
    uint64_t calls;
    double percentage;
} profile_entry_t;

typedef struct {
    profile_entry_t gf128_mul;
    profile_entry_t gf128_add;
    profile_entry_t gf128_inv;
    profile_entry_t sha3_hash;
    profile_entry_t merkle_build;
    profile_entry_t merkle_verify;
    profile_entry_t sumcheck_eval;
    profile_entry_t polynomial_eval;
    profile_entry_t multilinear_eval;
    profile_entry_t raa_encode;
    profile_entry_t transcript_update;
    uint64_t total_cycles;
} cpu_profile_t;

static cpu_profile_t g_profile = {0};

// Profile GF128 operations
void profile_gf128_operations(size_t iterations) {
    printf("\n=== GF(2^128) Operation Profiling ===\n");
    
    // Initialize test values
    gf128_t a = gf128_from_u64(0x123456789ABCDEF0ULL);
    gf128_t b = gf128_from_u64(0xFEDCBA9876543210ULL);
    gf128_t result;
    
    // Profile multiplication
    uint64_t start = rdtsc();
    for (size_t i = 0; i < iterations; i++) {
        result = gf128_mul(a, b);
        a = result; // Prevent optimization
    }
    uint64_t mul_cycles = rdtsc() - start;
    g_profile.gf128_mul.cycles = mul_cycles;
    g_profile.gf128_mul.calls = iterations;
    
    // Profile addition (XOR)
    start = rdtsc();
    for (size_t i = 0; i < iterations; i++) {
        result = gf128_add(a, b);
        b = result; // Prevent optimization
    }
    uint64_t add_cycles = rdtsc() - start;
    g_profile.gf128_add.cycles = add_cycles;
    g_profile.gf128_add.calls = iterations;
    
    // Profile inversion
    start = rdtsc();
    for (size_t i = 0; i < iterations/100; i++) { // Fewer iterations as it's expensive
        result = gf128_inv(a);
        a = gf128_add(a, gf128_one()); // Prevent zero
    }
    uint64_t inv_cycles = rdtsc() - start;
    g_profile.gf128_inv.cycles = inv_cycles * 100; // Scale up
    g_profile.gf128_inv.calls = iterations;
    
    printf("GF128 multiply: %.2f cycles/op\n", (double)mul_cycles / iterations);
    printf("GF128 add (XOR): %.2f cycles/op\n", (double)add_cycles / iterations);
    printf("GF128 invert: %.2f cycles/op\n", (double)inv_cycles * 100 / iterations);
}

// Profile SHA3 hashing
void profile_sha3_operations(size_t iterations) {
    printf("\n=== SHA3-256 Hashing Profiling ===\n");
    
    uint8_t data[136] = {0}; // One block
    uint8_t hash[32];
    
    // Single block hashing
    uint64_t start = rdtsc();
    for (size_t i = 0; i < iterations; i++) {
        sha3_256(data, sizeof(data), hash);
        data[0] = hash[0]; // Prevent optimization
    }
    uint64_t hash_cycles = rdtsc() - start;
    g_profile.sha3_hash.cycles = hash_cycles;
    g_profile.sha3_hash.calls = iterations;
    
    printf("SHA3-256 (136 bytes): %.2f cycles/op\n", (double)hash_cycles / iterations);
    printf("Throughput: %.2f MB/s @ 3GHz\n", 
           (double)iterations * 136 * 3e9 / (hash_cycles * 1e6));
}

// Profile polynomial evaluation
void profile_polynomial_operations(size_t num_variables) {
    printf("\n=== Polynomial Evaluation Profiling ===\n");
    
    size_t size = 1ULL << num_variables;
    gf128_t* poly = aligned_alloc(64, size * sizeof(gf128_t));
    gf128_t* point = aligned_alloc(64, num_variables * sizeof(gf128_t));
    
    // Initialize with random values
    for (size_t i = 0; i < size; i++) {
        poly[i] = gf128_from_u64(i);
    }
    for (size_t i = 0; i < num_variables; i++) {
        point[i] = gf128_from_u64(i + 1);
    }
    
    // Profile multilinear evaluation
    uint64_t start = rdtsc();
    gf128_t result = gf128_zero();
    
    // Simplified multilinear evaluation
    for (size_t i = 0; i < size; i++) {
        gf128_t term = poly[i];
        for (size_t j = 0; j < num_variables; j++) {
            if (i & (1ULL << j)) {
                term = gf128_mul(term, point[j]);
            } else {
                term = gf128_mul(term, gf128_sub(gf128_one(), point[j]));
            }
        }
        result = gf128_add(result, term);
    }
    
    uint64_t eval_cycles = rdtsc() - start;
    g_profile.multilinear_eval.cycles = eval_cycles;
    g_profile.multilinear_eval.calls = 1;
    
    printf("Multilinear eval (2^%zu): %.2f M cycles\n", 
           num_variables, (double)eval_cycles / 1e6);
    printf("Per-element cost: %.2f cycles\n", (double)eval_cycles / size);
    
    free(poly);
    free(point);
}

// Profile sumcheck round
void profile_sumcheck_round(size_t num_variables) {
    printf("\n=== Sumcheck Round Profiling ===\n");
    
    size_t half_size = 1ULL << (num_variables - 1);
    gf128_t* values = aligned_alloc(64, half_size * 2 * sizeof(gf128_t));
    
    // Initialize
    for (size_t i = 0; i < half_size * 2; i++) {
        values[i] = gf128_from_u64(i);
    }
    
    // Profile one sumcheck round
    uint64_t start = rdtsc();
    
    // Compute g(0), g(1), g(2) for degree-3 polynomial
    gf128_t g0 = gf128_zero();
    gf128_t g1 = gf128_zero();
    gf128_t g2 = gf128_zero();
    
    for (size_t i = 0; i < half_size; i++) {
        gf128_t v0 = values[2*i];
        gf128_t v1 = values[2*i + 1];
        
        // g(0) = sum of v0
        g0 = gf128_add(g0, v0);
        
        // g(1) = sum of v1
        g1 = gf128_add(g1, v1);
        
        // g(2) = sum of 2*v0 + v1
        gf128_t two = gf128_from_u64(2);
        g2 = gf128_add(g2, gf128_add(gf128_mul(two, v0), v1));
    }
    
    uint64_t round_cycles = rdtsc() - start;
    g_profile.sumcheck_eval.cycles = round_cycles;
    g_profile.sumcheck_eval.calls = 1;
    
    printf("Sumcheck round (2^%zu elements): %.2f K cycles\n", 
           num_variables, (double)round_cycles / 1e3);
    printf("Per-element cost: %.2f cycles\n", (double)round_cycles / half_size);
    
    free(values);
}

// Profile RAA encoding
void profile_raa_encoding(size_t message_size) {
    printf("\n=== RAA Encoding Profiling ===\n");
    
    const size_t repetition = 4;
    size_t codeword_size = message_size * repetition;
    
    gf128_t* message = aligned_alloc(64, message_size * sizeof(gf128_t));
    gf128_t* codeword = aligned_alloc(64, codeword_size * sizeof(gf128_t));
    uint32_t* perm1 = aligned_alloc(64, codeword_size * sizeof(uint32_t));
    uint32_t* perm2 = aligned_alloc(64, codeword_size * sizeof(uint32_t));
    
    // Initialize
    for (size_t i = 0; i < message_size; i++) {
        message[i] = gf128_from_u64(i);
    }
    for (size_t i = 0; i < codeword_size; i++) {
        perm1[i] = i;
        perm2[i] = (i * 7919 + 4933) % codeword_size; // Pseudo-random
    }
    
    uint64_t start = rdtsc();
    
    // Step 1: Repeat
    for (size_t i = 0; i < message_size; i++) {
        for (size_t j = 0; j < repetition; j++) {
            codeword[i * repetition + j] = message[i];
        }
    }
    
    // Step 2: Permute and accumulate (P1)
    gf128_t* temp = aligned_alloc(64, codeword_size * sizeof(gf128_t));
    for (size_t i = 0; i < codeword_size; i++) {
        temp[i] = codeword[perm1[i]];
    }
    for (size_t i = 1; i < codeword_size; i++) {
        temp[i] = gf128_add(temp[i], temp[i-1]);
    }
    
    // Step 3: Permute and accumulate (P2)
    for (size_t i = 0; i < codeword_size; i++) {
        codeword[i] = temp[perm2[i]];
    }
    for (size_t i = 1; i < codeword_size; i++) {
        codeword[i] = gf128_add(codeword[i], codeword[i-1]);
    }
    
    uint64_t encode_cycles = rdtsc() - start;
    g_profile.raa_encode.cycles = encode_cycles;
    g_profile.raa_encode.calls = 1;
    
    printf("RAA encode (%zu -> %zu): %.2f M cycles\n", 
           message_size, codeword_size, (double)encode_cycles / 1e6);
    printf("Per-element cost: %.2f cycles\n", (double)encode_cycles / codeword_size);
    
    free(message);
    free(codeword);
    free(perm1);
    free(perm2);
    free(temp);
}

// Generate detailed report
void generate_cpu_report() {
    printf("\n=== CPU Profiling Summary ===\n");
    printf("%-25s %15s %12s %10s %8s\n", 
           "Operation", "Total Cycles", "Calls", "Cycles/Op", "Percent");
    printf("%-25s %15s %12s %10s %8s\n", 
           "---------", "------------", "-----", "---------", "-------");
    
    // Calculate total cycles
    g_profile.total_cycles = 
        g_profile.gf128_mul.cycles +
        g_profile.gf128_add.cycles +
        g_profile.gf128_inv.cycles +
        g_profile.sha3_hash.cycles +
        g_profile.sumcheck_eval.cycles +
        g_profile.multilinear_eval.cycles +
        g_profile.raa_encode.cycles;
    
    // Print each operation
    profile_entry_t* entries[] = {
        &g_profile.gf128_mul,
        &g_profile.gf128_add,
        &g_profile.gf128_inv,
        &g_profile.sha3_hash,
        &g_profile.sumcheck_eval,
        &g_profile.multilinear_eval,
        &g_profile.raa_encode
    };
    
    const char* names[] = {
        "GF128 Multiplication",
        "GF128 Addition (XOR)",
        "GF128 Inversion",
        "SHA3-256 Hashing",
        "Sumcheck Round",
        "Multilinear Evaluation",
        "RAA Encoding"
    };
    
    for (size_t i = 0; i < 7; i++) {
        entries[i]->name = names[i];
        entries[i]->percentage = 100.0 * entries[i]->cycles / g_profile.total_cycles;
        
        printf("%-25s %15llu %12llu %10.2f %7.1f%%\n",
               entries[i]->name,
               entries[i]->cycles,
               entries[i]->calls,
               entries[i]->calls > 0 ? (double)entries[i]->cycles / entries[i]->calls : 0,
               entries[i]->percentage);
    }
    
    printf("\nTotal cycles: %.2f M\n", g_profile.total_cycles / 1e6);
    printf("@ 3 GHz: %.2f ms\n", g_profile.total_cycles / 3e6);
    
    // Identify hotspots
    printf("\n=== Performance Hotspots ===\n");
    for (size_t i = 0; i < 7; i++) {
        if (entries[i]->percentage > 20.0) {
            printf("🔥 %s: %.1f%% - PRIMARY OPTIMIZATION TARGET\n", 
                   entries[i]->name, entries[i]->percentage);
        }
    }
}

int main() {
    printf("=== BaseFold RAA CPU Profiling Tool ===\n");
    printf("Measuring cycle counts for key operations...\n");
    
    // Profile different components
    profile_gf128_operations(1000000);
    profile_sha3_operations(10000);
    profile_polynomial_operations(16); // 2^16 = 65K elements
    profile_sumcheck_round(16);
    profile_raa_encoding(65536);
    
    // Generate report
    generate_cpu_report();
    
    return 0;
}