#ifndef SUMCHECK_WORKER_POOL_H
#define SUMCHECK_WORKER_POOL_H

#define _GNU_SOURCE
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include "gf128.h"

// Lock-free work queue for sumcheck tasks
typedef struct {
    enum {
        WORK_NONE = 0,
        WORK_SUM_PAIRS,
        WORK_FOLD_BUFFER,
        WORK_SHUTDOWN
    } type;
    
    // Work parameters
    gf128_t* buffer;
    gf128_t* new_buffer;
    size_t start;
    size_t end;
    gf128_t challenge;
    
    // Results
    gf128_t sum_0;
    gf128_t sum_1;
} work_item_t;

// Worker thread state
typedef struct {
    pthread_t thread;
    int worker_id;
    
    // Work queue (single producer, single consumer)
    work_item_t work;
    atomic_bool has_work;
    atomic_bool work_done;
    
    // CPU affinity and capabilities
    int cpu_core;
    bool has_avx2;
    bool has_avx512;
    
    // Statistics
    size_t tasks_completed;
    double total_time;
} worker_state_t;

// Global worker pool
typedef struct {
    worker_state_t* workers;
    int num_workers;
    bool initialized;
    
    // Round-robin work distribution
    atomic_int next_worker;
} worker_pool_t;

// Initialize global worker pool (called once at startup)
void sumcheck_workers_init(int num_threads);

// Submit sum work to pool (non-blocking)
void sumcheck_submit_sum_work(
    gf128_t* buffer,
    size_t total_half,
    gf128_t* sum_0_out,
    gf128_t* sum_1_out);

// Submit fold work to pool (non-blocking)
void sumcheck_submit_fold_work(
    gf128_t* eval_buffer,
    gf128_t* new_buffer,
    size_t half,
    gf128_t challenge);

// Wait for all work to complete
void sumcheck_wait_completion(void);

// Shutdown worker pool (called once at exit)
void sumcheck_workers_shutdown(void);

// Get global pool instance
worker_pool_t* sumcheck_get_pool(void);

#endif // SUMCHECK_WORKER_POOL_H