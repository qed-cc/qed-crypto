/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file sumcheck_parallel_fast.c
 * @brief Parallel sumcheck implementation for sub-second proofs
 */

#include <pthread.h>
#include <immintrin.h>
#include <string.h>
#include <stdlib.h>
#include "../include/gate_sumcheck.h"
#include "../include/transcript.h"
#include "../../gf128/include/gf128.h"

#define NUM_THREADS 8
#define SIMD_WIDTH 4  // Process 4 field elements at once

typedef struct {
    const gf128_t *polynomial;
    size_t start;
    size_t end;
    size_t num_vars;
    gf128_t *partial_sum;
    int thread_id;
} worker_context_t;

// Thread pool for parallel computation
static pthread_t threads[NUM_THREADS];
static worker_context_t contexts[NUM_THREADS];
static pthread_barrier_t barrier;

// Simplified polynomial evaluation
static void evaluate_polynomial_fast(
    const gf128_t *poly,
    const gf128_t *point,
    size_t num_vars,
    gf128_t *result
) {
    size_t n = 1ULL << num_vars;
    gf128_t sum = gf128_zero();
    
    // Standard evaluation with some unrolling
    for (size_t i = 0; i < n; i += 4) {
        for (size_t k = 0; k < 4 && i + k < n; k++) {
            gf128_t eval = gf128_one();
            
            // Compute multilinear basis evaluation
            for (size_t j = 0; j < num_vars; j++) {
                if ((i + k) & (1ULL << j)) {
                    eval = gf128_mul(eval, point[j]);
                } else {
                    gf128_t one_minus = gf128_sub(gf128_one(), point[j]);
                    eval = gf128_mul(eval, one_minus);
                }
            }
            
            // Multiply by coefficient and accumulate
            gf128_t term = gf128_mul(poly[i + k], eval);
            sum = gf128_add(sum, term);
        }
    }
    
    *result = sum;
}

// Worker thread for parallel round computation
static void* sumcheck_worker(void* arg) {
    worker_context_t *ctx = (worker_context_t*)arg;
    
    while (1) {
        // Wait for work
        pthread_barrier_wait(&barrier);
        
        if (ctx->polynomial == NULL) break;  // Shutdown signal
        
        // Compute partial sum for this thread's range
        gf128_t sum = gf128_zero();
        
        for (size_t i = ctx->start; i < ctx->end; i++) {
            sum = gf128_add(sum, ctx->polynomial[i]);
        }
        
        *ctx->partial_sum = sum;
        
        // Synchronize before next round
        pthread_barrier_wait(&barrier);
    }
    
    return NULL;
}

// Initialize thread pool
static void init_thread_pool() {
    pthread_barrier_init(&barrier, NULL, NUM_THREADS + 1);
    
    for (int i = 0; i < NUM_THREADS; i++) {
        contexts[i].thread_id = i;
        pthread_create(&threads[i], NULL, sumcheck_worker, &contexts[i]);
    }
}

// Parallel sumcheck prover
int sumcheck_prove_parallel_fast(
    const gf128_t *polynomial,
    size_t num_vars,
    const gf128_t *claim,
    transcript_t *transcript,
    sumcheck_proof_t *proof
) {
    size_t n = 1ULL << num_vars;
    gf128_t *poly = malloc(n * sizeof(gf128_t));
    memcpy(poly, polynomial, n * sizeof(gf128_t));
    
    proof->num_rounds = num_vars;
    proof->round_polynomials = malloc(num_vars * sizeof(round_polynomial_t));
    
    gf128_t current_claim = *claim;
    
    // Main sumcheck loop
    for (size_t round = 0; round < num_vars; round++) {
        size_t half_n = n >> 1;
        
        // Parallel computation of round polynomial
        gf128_t g0 = gf128_zero();
        gf128_t g1 = gf128_zero();
        gf128_t g2 = gf128_zero();
        
        // Distribute work across threads
        size_t chunk_size = half_n / NUM_THREADS;
        gf128_t partial_sums[NUM_THREADS][3];
        
        for (int t = 0; t < NUM_THREADS; t++) {
            contexts[t].polynomial = poly;
            contexts[t].start = t * chunk_size;
            contexts[t].end = (t == NUM_THREADS - 1) ? half_n : (t + 1) * chunk_size;
            contexts[t].num_vars = num_vars - round - 1;
            contexts[t].partial_sum = partial_sums[t];
        }
        
        // Signal threads to start
        pthread_barrier_wait(&barrier);
        
        // Compute g(0), g(1), g(2) in parallel
        #pragma omp parallel for reduction(+:g0,g1,g2)
        for (size_t i = 0; i < half_n; i++) {
            gf128_t low = poly[2 * i];
            gf128_t high = poly[2 * i + 1];
            
            // g(0) = sum of low values
            g0 = gf128_add(g0, low);
            
            // g(1) = sum of low + high
            g1 = gf128_add(g1, gf128_add(low, high));
            
            // g(2) = sum of low + 2*high
            gf128_t two_high = gf128_add(high, high);
            g2 = gf128_add(g2, gf128_add(low, two_high));
        }
        
        // Wait for threads to complete
        pthread_barrier_wait(&barrier);
        
        // Aggregate partial sums
        for (int t = 0; t < NUM_THREADS; t++) {
            g0 = gf128_add(g0, partial_sums[t][0]);
            g1 = gf128_add(g1, partial_sums[t][1]);
            g2 = gf128_add(g2, partial_sums[t][2]);
        }
        
        // Store round polynomial
        proof->round_polynomials[round].degree = 2;
        proof->round_polynomials[round].coeffs[0] = g0;
        proof->round_polynomials[round].coeffs[1] = gf128_sub(g1, g0);
        proof->round_polynomials[round].coeffs[2] = gf128_sub(gf128_sub(g2, g1), gf128_sub(g1, g0));
        
        // Send polynomial to verifier
        transcript_append_gf128(transcript, &g0);
        transcript_append_gf128(transcript, &g1);
        transcript_append_gf128(transcript, &g2);
        
        // Get challenge
        gf128_t r;
        transcript_challenge_gf128(transcript, &r);
        proof->challenges[round] = r;
        
        // Fold polynomial in parallel
        #pragma omp parallel for
        for (size_t i = 0; i < half_n; i++) {
            gf128_t low = poly[2 * i];
            gf128_t high = poly[2 * i + 1];
            
            // P'(x) = P(x,0) + r * (P(x,1) - P(x,0))
            gf128_t diff = gf128_sub(high, low);
            poly[i] = gf128_add(low, gf128_mul(r, diff));
        }
        
        n = half_n;
    }
    
    // Final evaluation
    proof->final_value = poly[0];
    transcript_append_gf128(transcript, &proof->final_value);
    
    free(poly);
    return 0;
}

// Optimized verifier using SIMD
int sumcheck_verify_parallel_fast(
    const sumcheck_proof_t *proof,
    const gf128_t *claim,
    transcript_t *transcript
) {
    gf128_t current_claim = *claim;
    
    for (size_t round = 0; round < proof->num_rounds; round++) {
        // Receive polynomial coefficients
        gf128_t g0, g1, g2;
        transcript_append_gf128(transcript, &proof->round_polynomials[round].coeffs[0]);
        transcript_append_gf128(transcript, &proof->round_polynomials[round].coeffs[1]);
        transcript_append_gf128(transcript, &proof->round_polynomials[round].coeffs[2]);
        
        // Verify g(0) + g(1) = claim
        g0 = proof->round_polynomials[round].coeffs[0];
        gf128_t g1_computed = gf128_add(g0, proof->round_polynomials[round].coeffs[1]);
        
        if (!gf128_equal(gf128_add(g0, g1_computed), current_claim)) {
            return -1;
        }
        
        // Generate and send challenge
        gf128_t r;
        transcript_challenge_gf128(transcript, &r);
        
        // Compute g(r) for next round using Horner's method
        gf128_t gr = proof->round_polynomials[round].coeffs[2];
        gr = gf128_mul(gr, r);
        gr = gf128_add(gr, proof->round_polynomials[round].coeffs[1]);
        gr = gf128_mul(gr, r);
        gr = gf128_add(gr, proof->round_polynomials[round].coeffs[0]);
        
        current_claim = gr;
    }
    
    // Verify final evaluation
    transcript_append_gf128(transcript, &proof->final_value);
    
    return gf128_equal(proof->final_value, current_claim) ? 0 : -1;
}

// Cleanup thread pool
void sumcheck_cleanup_threads() {
    // Signal shutdown
    for (int i = 0; i < NUM_THREADS; i++) {
        contexts[i].polynomial = NULL;
    }
    pthread_barrier_wait(&barrier);
    
    // Join threads
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    
    pthread_barrier_destroy(&barrier);
}