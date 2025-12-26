#define _GNU_SOURCE
#include "sumcheck_worker_pool.h"
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <unistd.h>
#include <stdio.h>
#include <time.h>

#ifdef __x86_64__
#include <cpuid.h>
#include <immintrin.h>
#endif

// Global pool instance
static worker_pool_t* g_pool = NULL;

// Forward declarations for AVX functions from gate_sumcheck_multilinear_fast.c
extern void gf128_sum_pairs_avx2(gf128_t* sum_0, gf128_t* sum_1, const gf128_t* buffer, size_t half);
extern void gf128_sum_pairs_avx512(gf128_t* sum_0, gf128_t* sum_1, const gf128_t* buffer, size_t half);

// Optimized scalar sum for small chunks
static inline void sum_pairs_scalar(
    gf128_t* sum_0, gf128_t* sum_1,
    const gf128_t* buffer, size_t start, size_t end)
{
    // Unroll by 4 for better ILP
    size_t i = start;
    for (; i + 3 < end; i += 4) {
        *sum_0 = gf128_add(*sum_0, buffer[2 * i]);
        *sum_1 = gf128_add(*sum_1, buffer[2 * i + 1]);
        *sum_0 = gf128_add(*sum_0, buffer[2 * (i + 1)]);
        *sum_1 = gf128_add(*sum_1, buffer[2 * (i + 1) + 1]);
        *sum_0 = gf128_add(*sum_0, buffer[2 * (i + 2)]);
        *sum_1 = gf128_add(*sum_1, buffer[2 * (i + 2) + 1]);
        *sum_0 = gf128_add(*sum_0, buffer[2 * (i + 3)]);
        *sum_1 = gf128_add(*sum_1, buffer[2 * (i + 3) + 1]);
    }
    
    // Handle remaining
    for (; i < end; i++) {
        *sum_0 = gf128_add(*sum_0, buffer[2 * i]);
        *sum_1 = gf128_add(*sum_1, buffer[2 * i + 1]);
    }
}

// Worker thread main loop
static void* worker_thread_main(void* arg) {
    worker_state_t* state = (worker_state_t*)arg;
    
    // Pin to CPU core
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(state->cpu_core, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    
    // Detect CPU features for this core
    #ifdef __x86_64__
    unsigned int eax, ebx, ecx, edx;
    if (__get_cpuid_max(0, NULL) >= 7) {
        __cpuid_count(7, 0, eax, ebx, ecx, edx);
        state->has_avx2 = (ebx & (1 << 5)) ? true : false;
        state->has_avx512 = (ebx & (1 << 16)) ? true : false;
    }
    #endif
    
    while (1) {
        // Spin-wait for work (low latency)
        while (!atomic_load(&state->has_work)) {
            __builtin_ia32_pause(); // CPU hint for spin loop
        }
        
        work_item_t work = state->work;
        
        if (work.type == WORK_SHUTDOWN) {
            break;
        }
        
        // Process work based on type
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        if (work.type == WORK_SUM_PAIRS) {
            gf128_t sum_0 = gf128_zero();
            gf128_t sum_1 = gf128_zero();
            
            size_t chunk_size = work.end - work.start;
            
            #ifdef __x86_64__
            // Use AVX for larger chunks
            if (state->has_avx512 && chunk_size >= 64) {
                // Process most with AVX-512
                size_t avx_end = work.start + (chunk_size & ~7);
                gf128_sum_pairs_avx512(&sum_0, &sum_1, 
                    work.buffer + 2 * work.start, avx_end - work.start);
                // Handle remainder with scalar
                sum_pairs_scalar(&sum_0, &sum_1, work.buffer, avx_end, work.end);
            } else if (state->has_avx2 && chunk_size >= 32) {
                // Process most with AVX2
                size_t avx_end = work.start + (chunk_size & ~3);
                gf128_sum_pairs_avx2(&sum_0, &sum_1,
                    work.buffer + 2 * work.start, avx_end - work.start);
                // Handle remainder with scalar
                sum_pairs_scalar(&sum_0, &sum_1, work.buffer, avx_end, work.end);
            } else
            #endif
            {
                // Pure scalar for small chunks
                sum_pairs_scalar(&sum_0, &sum_1, work.buffer, work.start, work.end);
            }
            
            state->work.sum_0 = sum_0;
            state->work.sum_1 = sum_1;
            
        } else if (work.type == WORK_FOLD_BUFFER) {
            // Folding implementation
            gf128_t one_minus_r = gf128_add(gf128_one(), work.challenge);
            
            // Create multiplication contexts
            gf128_mul_ctx_t ctx_r, ctx_om;
            gf128_mul_ctx_init(&ctx_r, work.challenge);
            gf128_mul_ctx_init(&ctx_om, one_minus_r);
            
            // Process the fold
            for (size_t i = work.start; i < work.end; i++) {
                gf128_t even_val = work.buffer[2 * i];
                gf128_t odd_val = work.buffer[2 * i + 1];
                
                gf128_t t0 = gf128_mul_ctx_mul(&ctx_om, even_val);
                gf128_t t1 = gf128_mul_ctx_mul(&ctx_r, odd_val);
                
                work.new_buffer[i] = gf128_add(t0, t1);
            }
        }
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        state->total_time += (end.tv_sec - start.tv_sec) + 
                            (end.tv_nsec - start.tv_nsec) / 1e9;
        state->tasks_completed++;
        
        // Signal completion
        atomic_store(&state->work_done, true);
        atomic_store(&state->has_work, false);
    }
    
    return NULL;
}

void sumcheck_workers_init(int num_threads) {
    if (g_pool) return; // Already initialized
    
    g_pool = calloc(1, sizeof(worker_pool_t));
    g_pool->num_workers = num_threads;
    g_pool->workers = calloc(num_threads, sizeof(worker_state_t));
    
    
    // Get number of CPU cores
    int num_cores = sysconf(_SC_NPROCESSORS_ONLN);
    
    // Create worker threads
    for (int i = 0; i < num_threads; i++) {
        worker_state_t* worker = &g_pool->workers[i];
        worker->worker_id = i;
        worker->cpu_core = i % num_cores; // Distribute across cores
        atomic_store(&worker->has_work, false);
        atomic_store(&worker->work_done, false);
        
        pthread_create(&worker->thread, NULL, worker_thread_main, worker);
    }
    
    g_pool->initialized = true;
    
    // Warm up the workers with dummy work
    for (int i = 0; i < num_threads; i++) {
        worker_state_t* worker = &g_pool->workers[i];
        worker->work.type = WORK_SUM_PAIRS;
        worker->work.start = 0;
        worker->work.end = 1;
        atomic_store(&worker->has_work, true);
    }
    
    // Wait for warmup
    for (int i = 0; i < num_threads; i++) {
        while (!atomic_load(&g_pool->workers[i].work_done)) {
            __builtin_ia32_pause();
        }
        atomic_store(&g_pool->workers[i].work_done, false);
    }
}

void sumcheck_submit_sum_work(
    gf128_t* buffer,
    size_t total_half,
    gf128_t* sum_0_out,
    gf128_t* sum_1_out)
{
    if (!g_pool || g_pool->num_workers == 0) {
        // Fallback to single-threaded
        sum_pairs_scalar(sum_0_out, sum_1_out, buffer, 0, total_half);
        return;
    }
    
    // Distribute work among workers
    size_t chunk_size = (total_half + g_pool->num_workers - 1) / g_pool->num_workers;
    
    // Submit work to all workers
    for (int i = 0; i < g_pool->num_workers; i++) {
        worker_state_t* worker = &g_pool->workers[i];
        
        size_t start = i * chunk_size;
        size_t end = start + chunk_size;
        if (end > total_half) end = total_half;
        if (start >= total_half) break;
        
        worker->work.type = WORK_SUM_PAIRS;
        worker->work.buffer = buffer;
        worker->work.start = start;
        worker->work.end = end;
        
        // Release the worker
        atomic_store(&worker->has_work, true);
    }
    
    // Wait for all workers to complete and accumulate results
    gf128_t total_sum_0 = gf128_zero();
    gf128_t total_sum_1 = gf128_zero();
    
    for (int i = 0; i < g_pool->num_workers; i++) {
        worker_state_t* worker = &g_pool->workers[i];
        
        if (i * chunk_size >= total_half) break;
        
        // Spin-wait for completion
        while (!atomic_load(&worker->work_done)) {
            __builtin_ia32_pause();
        }
        
        total_sum_0 = gf128_add(total_sum_0, worker->work.sum_0);
        total_sum_1 = gf128_add(total_sum_1, worker->work.sum_1);
        
        atomic_store(&worker->work_done, false);
    }
    
    *sum_0_out = total_sum_0;
    *sum_1_out = total_sum_1;
}

void sumcheck_submit_fold_work(
    gf128_t* eval_buffer,
    gf128_t* new_buffer,
    size_t half,
    gf128_t challenge)
{
    if (!g_pool || g_pool->num_workers == 0 || half < 1024) {
        // Single-threaded for small problems
        gf128_t one_minus_r = gf128_add(gf128_one(), challenge);
        gf128_mul_ctx_t ctx_r, ctx_om;
        gf128_mul_ctx_init(&ctx_r, challenge);
        gf128_mul_ctx_init(&ctx_om, one_minus_r);
        
        for (size_t i = 0; i < half; i++) {
            gf128_t even_val = eval_buffer[2 * i];
            gf128_t odd_val = eval_buffer[2 * i + 1];
            
            gf128_t t0 = gf128_mul_ctx_mul(&ctx_om, even_val);
            gf128_t t1 = gf128_mul_ctx_mul(&ctx_r, odd_val);
            
            new_buffer[i] = gf128_add(t0, t1);
        }
        return;
    }
    
    // Distribute folding work
    size_t chunk_size = (half + g_pool->num_workers - 1) / g_pool->num_workers;
    
    for (int i = 0; i < g_pool->num_workers; i++) {
        worker_state_t* worker = &g_pool->workers[i];
        
        size_t start = i * chunk_size;
        size_t end = start + chunk_size;
        if (end > half) end = half;
        if (start >= half) break;
        
        worker->work.type = WORK_FOLD_BUFFER;
        worker->work.buffer = eval_buffer;
        worker->work.new_buffer = new_buffer;
        worker->work.start = start;
        worker->work.end = end;
        worker->work.challenge = challenge;
        
        atomic_store(&worker->has_work, true);
    }
    
    // Wait for completion
    for (int i = 0; i < g_pool->num_workers; i++) {
        if (i * chunk_size >= half) break;
        
        while (!atomic_load(&g_pool->workers[i].work_done)) {
            __builtin_ia32_pause();
        }
        atomic_store(&g_pool->workers[i].work_done, false);
    }
}

void sumcheck_workers_shutdown(void) {
    if (!g_pool) return;
    
    // Send shutdown signal to all workers
    for (int i = 0; i < g_pool->num_workers; i++) {
        g_pool->workers[i].work.type = WORK_SHUTDOWN;
        atomic_store(&g_pool->workers[i].has_work, true);
    }
    
    // Wait for all workers to exit
    for (int i = 0; i < g_pool->num_workers; i++) {
        pthread_join(g_pool->workers[i].thread, NULL);
    }
    
    free(g_pool->workers);
    free(g_pool);
    g_pool = NULL;
}

worker_pool_t* sumcheck_get_pool(void) {
    return g_pool;
}