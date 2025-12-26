/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file proving_time_deep_profiler.c
 * @brief Deep profiling tool for BaseFold RAA proving time with detailed phase analysis
 * 
 * This tool provides microsecond-level profiling of every phase in proof generation,
 * identifying bottlenecks and optimization opportunities while maintaining 122+ bit soundness.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sched.h>
#include <sys/mman.h>
#include <immintrin.h>
#include <x86intrin.h>
#include "basefold_raa.h"
#include "sha3.h"
#include "circuit_io.h"
#include "evaluator.h"
#include "gf128.h"
#include "binary_ntt.h"
#include "merkle/build.h"
#include "transcript.h"
#include "multilinear.h"
#include "vanishing_poly.h"
#include "prg.h"
#include "secure_random.h"

// High-resolution timing
typedef struct {
    uint64_t start_cycles;
    uint64_t end_cycles;
    struct timespec start_time;
    struct timespec end_time;
} timing_t;

// Detailed phase breakdown
typedef struct {
    timing_t total;
    timing_t setup;
    timing_t witness_generation;
    timing_t zk_masking;
    timing_t sumcheck_total;
    timing_t sumcheck_rounds[32]; // Per-round timing
    timing_t binary_ntt;
    timing_t ntt_preparation;
    timing_t ntt_butterfly[32]; // Per-layer timing
    timing_t raa_encoding;
    timing_t raa_repeat;
    timing_t raa_permute1;
    timing_t raa_accumulate1;
    timing_t raa_permute2;
    timing_t raa_accumulate2;
    timing_t merkle_building;
    timing_t merkle_hashing;
    timing_t merkle_tree_construction;
    timing_t query_generation;
    timing_t query_opening[320]; // Per-query timing
    timing_t transcript_ops;
    timing_t memory_alloc;
    timing_t memory_access_patterns;
} phase_timing_t;

// Memory access patterns
typedef struct {
    uint64_t cache_misses_l1;
    uint64_t cache_misses_l2;
    uint64_t cache_misses_l3;
    uint64_t tlb_misses;
    uint64_t memory_bandwidth_used;
    uint64_t sequential_accesses;
    uint64_t random_accesses;
} memory_stats_t;

// Global profiling state
static phase_timing_t g_timing = {0};
static memory_stats_t g_memory = {0};
static int g_profiling_enabled = 1;

// CPU frequency detection
static double get_cpu_frequency() {
    uint64_t start = __rdtsc();
    struct timespec ts = {.tv_sec = 0, .tv_nsec = 100000000}; // 100ms
    nanosleep(&ts, NULL);
    uint64_t end = __rdtsc();
    return (double)(end - start) / 100000000.0; // cycles per nanosecond = GHz
}

// Start timing
static inline void start_timing(timing_t* t) {
    if (!g_profiling_enabled) return;
    t->start_cycles = __rdtsc();
    clock_gettime(CLOCK_MONOTONIC, &t->start_time);
}

// End timing
static inline void end_timing(timing_t* t) {
    if (!g_profiling_enabled) return;
    clock_gettime(CLOCK_MONOTONIC, &t->end_time);
    t->end_cycles = __rdtsc();
}

// Get elapsed microseconds
static inline double get_elapsed_us(const timing_t* t) {
    return (t->end_time.tv_sec - t->start_time.tv_sec) * 1000000.0 +
           (t->end_time.tv_nsec - t->start_time.tv_nsec) / 1000.0;
}

// Get elapsed cycles
static inline uint64_t get_elapsed_cycles(const timing_t* t) {
    return t->end_cycles - t->start_cycles;
}

// Custom memory allocator with profiling
static void* profiled_malloc(size_t size) {
    timing_t alloc_time;
    start_timing(&alloc_time);
    
    void* ptr = aligned_alloc(64, size); // Cache-line aligned
    
    end_timing(&alloc_time);
    g_timing.memory_alloc.end_cycles += get_elapsed_cycles(&alloc_time);
    
    // Prefetch for better cache behavior
    if (ptr && size >= 64) {
        _mm_prefetch((const char*)ptr, _MM_HINT_T0);
    }
    
    return ptr;
}

// Hooked witness generation with profiling
static void generate_sha3_witness_profiled(gf128_t* witness, size_t witness_size, 
                                          const uint8_t* input, size_t input_len) {
    start_timing(&g_timing.witness_generation);
    
    // Standard SHA3-256 circuit witness generation
    circuit_t circuit;
    uint8_t circuit_data[1000000];
    circuit.gates = (gate_t*)circuit_data;
    circuit.num_gates = 0;
    circuit.gate_capacity = sizeof(circuit_data) / sizeof(gate_t);
    
    // Generate SHA3 circuit
    generate_sha3_256_circuit(&circuit, input, input_len);
    
    // Evaluate to get witness
    evaluator_ctx_t eval_ctx;
    evaluator_init(&eval_ctx, circuit.num_gates);
    
    // Set input wires
    for (size_t i = 0; i < input_len * 8 && i < circuit.num_gates; i++) {
        size_t byte_idx = i / 8;
        size_t bit_idx = i % 8;
        bool bit_val = (input[byte_idx] >> bit_idx) & 1;
        evaluator_set_wire(&eval_ctx, i, bit_val ? gf128_one() : gf128_zero());
    }
    
    // Evaluate gates
    for (size_t i = 0; i < circuit.num_gates; i++) {
        const gate_t* g = &circuit.gates[i];
        gf128_t result = evaluator_eval_gate(&eval_ctx, g);
        evaluator_set_wire(&eval_ctx, g->output_wire, result);
    }
    
    // Extract witness values
    for (size_t i = 0; i < witness_size && i < eval_ctx.num_wires; i++) {
        witness[i] = eval_ctx.wire_values[i];
    }
    
    evaluator_cleanup(&eval_ctx);
    
    end_timing(&g_timing.witness_generation);
}

// Hooked ZK masking with profiling
static void apply_zk_masking_profiled(gf128_t* masked_witness, const gf128_t* witness,
                                     size_t n, const uint8_t* mask_seed) {
    start_timing(&g_timing.zk_masking);
    
    // Initialize PRG
    prg_init(mask_seed);
    
    // Generate and apply mask
    for (size_t i = 0; i < n; i++) {
        uint8_t rand_bytes[16];
        #ifdef __x86_64__
        __m128i prg_val = prg_next();
        _mm_storeu_si128((__m128i*)rand_bytes, prg_val);
        #else
        prg_next(rand_bytes);
        #endif
        
        gf128_t mask = gf128_from_bytes(rand_bytes);
        masked_witness[i] = gf128_add(witness[i], mask);
    }
    
    end_timing(&g_timing.zk_masking);
}

// Hooked sumcheck with per-round profiling
static void sumcheck_profiled(const gf128_t* witness, size_t num_variables,
                            gf128_t* sumcheck_responses, uint8_t* sumcheck_commitments,
                            fiat_shamir_t* transcript) {
    start_timing(&g_timing.sumcheck_total);
    
    size_t n = 1ULL << num_variables;
    gf128_t* current = profiled_malloc(n * sizeof(gf128_t));
    memcpy(current, witness, n * sizeof(gf128_t));
    
    for (size_t round = 0; round < num_variables; round++) {
        start_timing(&g_timing.sumcheck_rounds[round]);
        
        size_t current_size = 1ULL << (num_variables - round);
        
        // Compute univariate polynomial
        gf128_t g0 = gf128_zero();
        gf128_t g1 = gf128_zero();
        
        // Vectorized summation if possible
        #ifdef __AVX2__
        if (current_size >= 16) {
            // Process 2 GF128 elements at once
            for (size_t i = 0; i < current_size / 2; i += 2) {
                __m256i v0 = _mm256_loadu_si256((__m256i*)&current[2*i]);
                __m256i v1 = _mm256_loadu_si256((__m256i*)&current[2*i + 2]);
                
                // Extract and accumulate
                // TODO: Optimize with proper GF128 SIMD
            }
        }
        #endif
        
        // Standard accumulation
        for (size_t i = 0; i < current_size / 2; i++) {
            g0 = gf128_add(g0, current[2*i]);
            g1 = gf128_add(g1, current[2*i + 1]);
        }
        
        // Store responses
        sumcheck_responses[round * 3] = g0;
        sumcheck_responses[round * 3 + 1] = g1;
        sumcheck_responses[round * 3 + 2] = gf128_add(g0, g1);
        
        // Commit
        sha3_ctx commit_ctx;
        sha3_init(&commit_ctx, SHA3_256);
        sha3_update(&commit_ctx, (uint8_t*)&g0, sizeof(gf128_t));
        sha3_update(&commit_ctx, (uint8_t*)&g1, sizeof(gf128_t));
        sha3_final(&commit_ctx, sumcheck_commitments + round * 32, 32);
        
        // Update transcript
        fs_absorb(transcript, sumcheck_commitments + round * 32, 32);
        
        // Get challenge
        uint8_t challenge_bytes[16];
        uint8_t challenge_full[32];
        fs_challenge(transcript, challenge_full);
        memcpy(challenge_bytes, challenge_full, 16);
        gf128_t r_i = gf128_from_bytes(challenge_bytes);
        
        // Fold for next round
        gf128_t one_minus_r = gf128_add(gf128_one(), r_i);
        
        for (size_t i = 0; i < current_size / 2; i++) {
            current[i] = gf128_add(
                gf128_mul(one_minus_r, current[2*i]),
                gf128_mul(r_i, current[2*i + 1])
            );
        }
        
        end_timing(&g_timing.sumcheck_rounds[round]);
    }
    
    free(current);
    end_timing(&g_timing.sumcheck_total);
}

// Hooked Binary NTT with layer profiling
static void binary_ntt_profiled(const gf128_t* multilinear_evals, 
                               gf128_t* univariate_coeffs,
                               size_t num_variables) {
    start_timing(&g_timing.binary_ntt);
    
    // Preparation
    start_timing(&g_timing.ntt_preparation);
    binary_ntt_ctx_t* ntt_ctx = profiled_malloc(sizeof(binary_ntt_ctx_t));
    binary_ntt_init(ntt_ctx, num_variables);
    end_timing(&g_timing.ntt_preparation);
    
    size_t n = 1ULL << num_variables;
    memcpy(univariate_coeffs, multilinear_evals, n * sizeof(gf128_t));
    
    // Butterfly layers
    size_t stride = 2;
    for (size_t layer = 0; layer < num_variables; layer++) {
        start_timing(&g_timing.ntt_butterfly[layer]);
        
        // Profile memory access pattern
        uint64_t seq_accesses = 0;
        uint64_t rand_accesses = 0;
        
        for (size_t i = 0; i < n; i += stride) {
            for (size_t j = 0; j < stride / 2; j++) {
                size_t idx1 = i + j;
                size_t idx2 = i + j + stride / 2;
                
                // Butterfly operation
                gf128_t a = univariate_coeffs[idx1];
                gf128_t b = univariate_coeffs[idx2];
                
                univariate_coeffs[idx1] = gf128_add(a, b);
                univariate_coeffs[idx2] = gf128_add(a, gf128_mul(b, ntt_ctx->basis[layer]));
                
                // Track access pattern
                if (idx2 == idx1 + 1) seq_accesses++;
                else rand_accesses++;
            }
        }
        
        g_memory.sequential_accesses += seq_accesses;
        g_memory.random_accesses += rand_accesses;
        
        stride *= 2;
        end_timing(&g_timing.ntt_butterfly[layer]);
    }
    
    binary_ntt_free(ntt_ctx);
    free(ntt_ctx);
    
    end_timing(&g_timing.binary_ntt);
}

// Hooked RAA encoding with phase profiling
static void raa_encode_profiled(const gf128_t* message, size_t message_size,
                               gf128_t* codeword, const basefold_raa_params_t* params) {
    start_timing(&g_timing.raa_encoding);
    
    size_t codeword_len = params->codeword_len;
    gf128_t* temp = profiled_malloc(codeword_len * sizeof(gf128_t));
    
    // Phase 1: Repeat
    start_timing(&g_timing.raa_repeat);
    for (size_t i = 0; i < message_size; i++) {
        for (size_t j = 0; j < params->repetition_factor; j++) {
            codeword[i * params->repetition_factor + j] = message[i];
        }
    }
    end_timing(&g_timing.raa_repeat);
    
    // Phase 2: First permutation
    start_timing(&g_timing.raa_permute1);
    for (size_t i = 0; i < codeword_len; i++) {
        temp[i] = codeword[params->perm1[i]];
    }
    end_timing(&g_timing.raa_permute1);
    
    // Phase 3: First accumulation
    start_timing(&g_timing.raa_accumulate1);
    for (size_t i = 1; i < codeword_len; i++) {
        temp[i] = gf128_add(temp[i], temp[i-1]);
    }
    end_timing(&g_timing.raa_accumulate1);
    
    // Phase 4: Second permutation
    start_timing(&g_timing.raa_permute2);
    for (size_t i = 0; i < codeword_len; i++) {
        codeword[i] = temp[params->perm2[i]];
    }
    end_timing(&g_timing.raa_permute2);
    
    // Phase 5: Second accumulation
    start_timing(&g_timing.raa_accumulate2);
    for (size_t i = 1; i < codeword_len; i++) {
        codeword[i] = gf128_add(codeword[i], codeword[i-1]);
    }
    end_timing(&g_timing.raa_accumulate2);
    
    free(temp);
    end_timing(&g_timing.raa_encoding);
}

// Hooked Merkle tree building
static void merkle_build_profiled(const gf128_t* codeword, size_t num_leaves,
                                 merkle_tree_t* tree) {
    start_timing(&g_timing.merkle_building);
    
    // Hash leaves
    start_timing(&g_timing.merkle_hashing);
    uint8_t* leaf_hashes = profiled_malloc(num_leaves * 32);
    
    // Profile batched hashing
    for (size_t i = 0; i < num_leaves; i++) {
        sha3_256((uint8_t*)&codeword[i * 8], 8 * sizeof(gf128_t), 
                 leaf_hashes + i * 32);
    }
    end_timing(&g_timing.merkle_hashing);
    
    // Build tree structure
    start_timing(&g_timing.merkle_tree_construction);
    // ... tree construction logic ...
    end_timing(&g_timing.merkle_tree_construction);
    
    free(leaf_hashes);
    end_timing(&g_timing.merkle_building);
}

// Main profiling function
void profile_basefold_proving() {
    printf("=== BaseFold RAA Deep Proving Time Profiler ===\n");
    printf("Detecting CPU frequency...\n");
    double cpu_ghz = get_cpu_frequency();
    printf("CPU frequency: %.2f GHz\n\n", cpu_ghz);
    
    // Pin to CPU core for consistent measurements
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(0, &cpuset);
    sched_setaffinity(0, sizeof(cpuset), &cpuset);
    
    // Test parameters
    const size_t num_variables = 18; // 2^18 = 262K constraints
    const size_t witness_size = 1ULL << num_variables;
    const uint8_t input[] = "test input for SHA3-256 proving";
    
    printf("Test parameters:\n");
    printf("- Constraint system size: 2^%zu = %zu\n", num_variables, witness_size);
    printf("- Input: \"%s\"\n", input);
    printf("- Security: 122-bit post-quantum\n\n");
    
    // Initialize
    start_timing(&g_timing.total);
    start_timing(&g_timing.setup);
    
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .enable_zk = 1,
        .security_bits = 122
    };
    
    basefold_raa_proof_t proof;
    gf128_t* witness = profiled_malloc(witness_size * sizeof(gf128_t));
    
    end_timing(&g_timing.setup);
    
    // Generate witness
    generate_sha3_witness_profiled(witness, witness_size, input, sizeof(input));
    
    // Detailed proving with hooks
    printf("Running detailed proof generation with profiling...\n");
    
    // The actual basefold_raa_prove would be modified to call our profiled functions
    // For now, we simulate the main phases:
    
    // 1. ZK masking
    if (config.enable_zk) {
        uint8_t mask_seed[32];
        secure_random_seed_32(mask_seed);
        gf128_t* masked_witness = profiled_malloc(witness_size * sizeof(gf128_t));
        apply_zk_masking_profiled(masked_witness, witness, witness_size, mask_seed);
        free(masked_witness);
    }
    
    // 2. Sumcheck
    gf128_t* sumcheck_responses = profiled_malloc(num_variables * 3 * sizeof(gf128_t));
    uint8_t* sumcheck_commitments = profiled_malloc(num_variables * 32);
    fiat_shamir_t transcript;
    uint8_t seed[16];
    secure_random_seed_16(seed);
    fs_init_with_domain(&transcript, seed, "BASEFOLD_RAA_V1");
    
    sumcheck_profiled(witness, num_variables, sumcheck_responses, 
                     sumcheck_commitments, &transcript);
    
    // 3. Binary NTT
    gf128_t* univariate_coeffs = profiled_malloc(witness_size * sizeof(gf128_t));
    binary_ntt_profiled(witness, univariate_coeffs, num_variables);
    
    // 4. RAA encoding
    basefold_raa_params_t raa_params;
    uint8_t raa_seed[32];
    fs_challenge(&transcript, raa_seed);
    basefold_raa_init_params(&raa_params, witness_size, 4, raa_seed);
    
    gf128_t* raa_codeword = profiled_malloc(raa_params.codeword_len * sizeof(gf128_t));
    raa_encode_profiled(univariate_coeffs, witness_size, raa_codeword, &raa_params);
    
    // 5. Merkle tree building
    merkle_tree_t tree;
    merkle_build_profiled(raa_codeword, raa_params.codeword_len / 8, &tree);
    
    end_timing(&g_timing.total);
    
    // Generate detailed report
    printf("\n=== DETAILED TIMING BREAKDOWN ===\n");
    printf("Total proving time: %.2f ms (%.0f cycles)\n", 
           get_elapsed_us(&g_timing.total) / 1000.0,
           (double)get_elapsed_cycles(&g_timing.total));
    
    printf("\nPhase breakdown:\n");
    printf("%-30s %10s %10s %8s %10s\n", 
           "Phase", "Time (ms)", "Cycles", "Percent", "Cycles/Op");
    printf("%-30s %10s %10s %8s %10s\n", 
           "-----", "---------", "------", "-------", "---------");
    
    // Helper to print phase info
    #define PRINT_PHASE(name, timing, ops) do { \
        double ms = get_elapsed_us(&timing) / 1000.0; \
        uint64_t cycles = get_elapsed_cycles(&timing); \
        double percent = 100.0 * cycles / get_elapsed_cycles(&g_timing.total); \
        printf("%-30s %10.3f %10llu %7.1f%% %10.1f\n", \
               name, ms, cycles, percent, ops > 0 ? (double)cycles/ops : 0); \
    } while(0)
    
    PRINT_PHASE("Setup", g_timing.setup, 1);
    PRINT_PHASE("Witness generation", g_timing.witness_generation, witness_size);
    PRINT_PHASE("ZK masking", g_timing.zk_masking, config.enable_zk ? witness_size : 0);
    PRINT_PHASE("Sumcheck (total)", g_timing.sumcheck_total, num_variables);
    PRINT_PHASE("Binary NTT", g_timing.binary_ntt, witness_size);
    PRINT_PHASE("- Preparation", g_timing.ntt_preparation, 1);
    PRINT_PHASE("RAA encoding", g_timing.raa_encoding, raa_params.codeword_len);
    PRINT_PHASE("- Repeat", g_timing.raa_repeat, witness_size);
    PRINT_PHASE("- Permute 1", g_timing.raa_permute1, raa_params.codeword_len);
    PRINT_PHASE("- Accumulate 1", g_timing.raa_accumulate1, raa_params.codeword_len);
    PRINT_PHASE("- Permute 2", g_timing.raa_permute2, raa_params.codeword_len);
    PRINT_PHASE("- Accumulate 2", g_timing.raa_accumulate2, raa_params.codeword_len);
    PRINT_PHASE("Merkle building", g_timing.merkle_building, raa_params.codeword_len/8);
    PRINT_PHASE("- Hashing", g_timing.merkle_hashing, raa_params.codeword_len/8);
    PRINT_PHASE("- Tree construction", g_timing.merkle_tree_construction, 1);
    
    // Sumcheck round breakdown
    printf("\nSumcheck round breakdown:\n");
    for (size_t i = 0; i < num_variables; i++) {
        if (g_timing.sumcheck_rounds[i].end_cycles > 0) {
            char name[32];
            snprintf(name, sizeof(name), "  Round %zu", i);
            PRINT_PHASE(name, g_timing.sumcheck_rounds[i], 1ULL << (num_variables - i));
        }
    }
    
    // NTT butterfly breakdown
    printf("\nBinary NTT butterfly breakdown:\n");
    for (size_t i = 0; i < num_variables; i++) {
        if (g_timing.ntt_butterfly[i].end_cycles > 0) {
            char name[32];
            snprintf(name, sizeof(name), "  Layer %zu", i);
            PRINT_PHASE(name, g_timing.ntt_butterfly[i], witness_size);
        }
    }
    
    // Memory statistics
    printf("\n=== MEMORY ACCESS PATTERNS ===\n");
    printf("Sequential accesses: %llu\n", g_memory.sequential_accesses);
    printf("Random accesses: %llu\n", g_memory.random_accesses);
    printf("Sequential ratio: %.1f%%\n", 
           100.0 * g_memory.sequential_accesses / 
           (g_memory.sequential_accesses + g_memory.random_accesses));
    
    // Bottleneck analysis
    printf("\n=== BOTTLENECK ANALYSIS ===\n");
    
    typedef struct {
        const char* name;
        timing_t* timing;
        double percent;
    } bottleneck_t;
    
    bottleneck_t bottlenecks[] = {
        {"Sumcheck", &g_timing.sumcheck_total, 0},
        {"Binary NTT", &g_timing.binary_ntt, 0},
        {"RAA encoding", &g_timing.raa_encoding, 0},
        {"Merkle building", &g_timing.merkle_building, 0},
        {"Witness generation", &g_timing.witness_generation, 0}
    };
    
    for (size_t i = 0; i < 5; i++) {
        bottlenecks[i].percent = 100.0 * get_elapsed_cycles(bottlenecks[i].timing) /
                                get_elapsed_cycles(&g_timing.total);
    }
    
    // Sort by percentage
    for (size_t i = 0; i < 4; i++) {
        for (size_t j = i + 1; j < 5; j++) {
            if (bottlenecks[j].percent > bottlenecks[i].percent) {
                bottleneck_t temp = bottlenecks[i];
                bottlenecks[i] = bottlenecks[j];
                bottlenecks[j] = temp;
            }
        }
    }
    
    printf("Top bottlenecks:\n");
    for (size_t i = 0; i < 3; i++) {
        printf("%zu. %s: %.1f%% of total time\n", 
               i + 1, bottlenecks[i].name, bottlenecks[i].percent);
    }
    
    // Optimization recommendations
    printf("\n=== OPTIMIZATION RECOMMENDATIONS ===\n");
    
    // Check sumcheck efficiency
    double sumcheck_percent = 100.0 * get_elapsed_cycles(&g_timing.sumcheck_total) /
                             get_elapsed_cycles(&g_timing.total);
    if (sumcheck_percent > 40) {
        printf("🔥 Sumcheck is %.1f%% of proving time:\n", sumcheck_percent);
        printf("   - Consider SIMD vectorization for polynomial evaluation\n");
        printf("   - Implement cache-friendly folding patterns\n");
        printf("   - Use batched operations for multiple rounds\n");
    }
    
    // Check NTT efficiency
    double ntt_percent = 100.0 * get_elapsed_cycles(&g_timing.binary_ntt) /
                        get_elapsed_cycles(&g_timing.total);
    if (ntt_percent > 20) {
        printf("🔥 Binary NTT is %.1f%% of proving time:\n", ntt_percent);
        printf("   - Implement cache-oblivious butterfly algorithms\n");
        printf("   - Use AVX-512 for GF128 operations\n");
        printf("   - Consider bit-reversal optimizations\n");
    }
    
    // Check memory patterns
    double seq_ratio = 100.0 * g_memory.sequential_accesses / 
                      (g_memory.sequential_accesses + g_memory.random_accesses);
    if (seq_ratio < 70) {
        printf("⚠️  Poor memory access pattern (%.1f%% sequential):\n", seq_ratio);
        printf("   - Restructure data layout for better cache usage\n");
        printf("   - Consider memory prefetching strategies\n");
        printf("   - Use blocked algorithms to improve locality\n");
    }
    
    // Cleanup
    free(witness);
    free(sumcheck_responses);
    free(sumcheck_commitments);
    free(univariate_coeffs);
    free(raa_codeword);
    basefold_raa_free_params(&raa_params);
}

int main() {
    // Disable CPU frequency scaling for accurate measurements
    system("echo performance | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor > /dev/null 2>&1");
    
    profile_basefold_proving();
    
    return 0;
}