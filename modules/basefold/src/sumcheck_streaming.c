/**
 * @file sumcheck_streaming.c
 * @brief Optimal streaming sumcheck implementation
 * 
 * This implementation follows the optimization plan to achieve near-memory-bandwidth
 * performance for the sumcheck algorithm.
 */

#define _GNU_SOURCE
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <sched.h>
#include <pthread.h>
#include <immintrin.h>
#include <stdatomic.h>
#include "gate_sumcheck_multilinear.h"
#include "gf128.h"

#ifdef _OPENMP
#include <omp.h>
#endif

// Forward declarations from gate_sumcheck_multilinear_fast.c
extern int has_avx2;
extern int has_avx512f;
extern void detect_cpu_features(void);
extern void compute_round_polynomial_ml_fast(
    gate_sumcheck_ml_t* instance,
    size_t round,
    gf128_t* g_evals);

// Cache line size
#define CACHE_LINE_SIZE 64

// Optimal chunk size for L1 cache
#define L1_CHUNK_SIZE (32 * 1024)  // 32KB L1 data cache
#define L2_CHUNK_SIZE (256 * 1024) // 256KB L2 cache
#define L3_CHUNK_SIZE (8 * 1024 * 1024) // 8MB L3 cache per core

// Thread work structure aligned to cache line
typedef struct {
    // Aligned to cache line boundary
    __m512i accumulators[16] __attribute__((aligned(64)));
    size_t start_offset;
    size_t end_offset;
    int thread_id;
    int cpu_core;
    char padding[CACHE_LINE_SIZE - (sizeof(__m512i)*16 % CACHE_LINE_SIZE)];
} thread_work_t;

// Separated buffer for even/odd values
typedef struct {
    gf128_t* even_values;  // All even values contiguous
    gf128_t* odd_values;   // All odd values contiguous
    size_t count;
} separated_buffer_t;

// Lock-free coordination structure
typedef struct {
    atomic_int threads_ready;
    atomic_int threads_done;
    thread_work_t* work;
    size_t num_threads;
    gf128_t final_sum_even;
    gf128_t final_sum_odd;
} coordinator_t;

// Get system info
static size_t get_l3_cache_size() {
    // Typical values, could be detected at runtime
    return 8 * 1024 * 1024; // 8MB per core
}

static size_t get_num_cpus() {
    #ifdef _OPENMP
    return omp_get_num_procs();
    #else
    return 1;
    #endif
}

// Determine optimal thread count based on data size
static size_t determine_optimal_threads(size_t total_bytes) {
    size_t l3_size = get_l3_cache_size();
    size_t num_cpus = get_num_cpus();
    
    if (total_bytes <= L2_CHUNK_SIZE) {
        return 1; // Single thread optimal for small data
    } else if (total_bytes <= l3_size) {
        return 2; // Two threads share L3
    } else {
        // Each thread gets L3-sized chunk, but cap at CPU count
        size_t ideal_threads = (total_bytes + l3_size - 1) / l3_size;
        return ideal_threads > num_cpus ? num_cpus : ideal_threads;
    }
}

// One-time transformation to separate even/odd values
void separate_even_odd(
    const gf128_t* interleaved,
    separated_buffer_t* separated,
    size_t count)
{
    separated->count = count / 2;
    separated->even_values = aligned_alloc(64, separated->count * sizeof(gf128_t));
    separated->odd_values = aligned_alloc(64, separated->count * sizeof(gf128_t));
    
    #pragma omp parallel for if(count > 65536)
    for (size_t i = 0; i < separated->count; i++) {
        separated->even_values[i] = interleaved[2*i];
        separated->odd_values[i] = interleaved[2*i + 1];
    }
}

// AVX-512 streaming kernel for separated buffers
static void stream_sumcheck_avx512_separated(
    const gf128_t* even_buffer,
    const gf128_t* odd_buffer,
    thread_work_t* work)
{
    // Pin to CPU core
    #ifdef __linux__
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(work->cpu_core, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    #endif
    
    // Initialize 8 accumulators for even and 8 for odd
    __m512i acc_even[8], acc_odd[8];
    for (int i = 0; i < 8; i++) {
        acc_even[i] = _mm512_setzero_si512();
        acc_odd[i] = _mm512_setzero_si512();
    }
    
    const gf128_t* even_ptr = even_buffer + work->start_offset;
    const gf128_t* odd_ptr = odd_buffer + work->start_offset;
    const size_t count = work->end_offset - work->start_offset;
    
    // Prefetch first blocks
    for (int i = 0; i < 8; i++) {
        _mm_prefetch((const char*)(even_ptr + i * 4), _MM_HINT_T0);
        _mm_prefetch((const char*)(odd_ptr + i * 4), _MM_HINT_T0);
    }
    
    // Main streaming loop - process 32 GF128 elements at once
    size_t i = 0;
    for (; i + 31 < count; i += 32) {
        // Prefetch 512 bytes ahead
        _mm_prefetch((const char*)(even_ptr + i + 64), _MM_HINT_T0);
        _mm_prefetch((const char*)(odd_ptr + i + 64), _MM_HINT_T0);
        
        // Load and accumulate even values
        for (int j = 0; j < 8; j++) {
            __m512i even_val = _mm512_load_si512(even_ptr + i + j*4);
            acc_even[j] = _mm512_xor_si512(acc_even[j], even_val);
        }
        
        // Load and accumulate odd values
        for (int j = 0; j < 8; j++) {
            __m512i odd_val = _mm512_load_si512(odd_ptr + i + j*4);
            acc_odd[j] = _mm512_xor_si512(acc_odd[j], odd_val);
        }
    }
    
    // Handle remaining elements
    for (; i < count; i++) {
        gf128_t even_val = even_ptr[i];
        gf128_t odd_val = odd_ptr[i];
        
        // Add to first accumulator
        __m128i even_128 = _mm_loadu_si128((const __m128i*)&even_val);
        __m128i odd_128 = _mm_loadu_si128((const __m128i*)&odd_val);
        
        __m512i curr_even = acc_even[0];
        __m512i curr_odd = acc_odd[0];
        
        // Extract first 128 bits, XOR, and put back
        __m128i first_even = _mm512_extracti32x4_epi32(curr_even, 0);
        __m128i first_odd = _mm512_extracti32x4_epi32(curr_odd, 0);
        
        first_even = _mm_xor_si128(first_even, even_128);
        first_odd = _mm_xor_si128(first_odd, odd_128);
        
        acc_even[0] = _mm512_inserti32x4(curr_even, first_even, 0);
        acc_odd[0] = _mm512_inserti32x4(curr_odd, first_odd, 0);
    }
    
    // Store accumulators back
    for (int i = 0; i < 8; i++) {
        work->accumulators[i] = acc_even[i];
        work->accumulators[i+8] = acc_odd[i];
    }
}

// Streaming kernel for interleaved data (original layout)
static void stream_sumcheck_avx512_interleaved(
    const gf128_t* buffer,
    thread_work_t* work)
{
    // Pin to CPU core
    #ifdef __linux__
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(work->cpu_core, &cpuset);
    pthread_setaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    #endif
    
    // Initialize accumulators
    __m512i acc_even[4], acc_odd[4];
    for (int i = 0; i < 4; i++) {
        acc_even[i] = _mm512_setzero_si512();
        acc_odd[i] = _mm512_setzero_si512();
    }
    
    const gf128_t* ptr = buffer + work->start_offset;
    const gf128_t* end = buffer + work->end_offset;
    
    // Prefetch first block
    for (int i = 0; i < 4; i++) {
        _mm_prefetch((const char*)(ptr + i * 8), _MM_HINT_T0);
    }
    
    // Main streaming loop - process 32 GF128 elements (16 pairs)
    while (ptr + 31 < end) {
        // Prefetch ahead
        _mm_prefetch((const char*)(ptr + 64), _MM_HINT_T0);
        _mm_prefetch((const char*)(ptr + 72), _MM_HINT_T0);
        
        // Load 32 GF128 elements (512 bytes)
        __m512i data0 = _mm512_load_si512(ptr);      // elements 0-3
        __m512i data1 = _mm512_load_si512(ptr + 4);  // elements 4-7
        __m512i data2 = _mm512_load_si512(ptr + 8);  // elements 8-11
        __m512i data3 = _mm512_load_si512(ptr + 12); // elements 12-15
        __m512i data4 = _mm512_load_si512(ptr + 16); // elements 16-19
        __m512i data5 = _mm512_load_si512(ptr + 20); // elements 20-23
        __m512i data6 = _mm512_load_si512(ptr + 24); // elements 24-27
        __m512i data7 = _mm512_load_si512(ptr + 28); // elements 28-31
        
        // Deinterleave using shuffle - pairs data0,data1
        // Shuffle pattern: 0,2,4,6 from each pair
        __m512i even01 = _mm512_shuffle_i64x2(data0, data1, 0x88); // 10 00 10 00
        __m512i odd01 = _mm512_shuffle_i64x2(data0, data1, 0xDD);  // 11 01 11 01
        
        __m512i even23 = _mm512_shuffle_i64x2(data2, data3, 0x88);
        __m512i odd23 = _mm512_shuffle_i64x2(data2, data3, 0xDD);
        
        __m512i even45 = _mm512_shuffle_i64x2(data4, data5, 0x88);
        __m512i odd45 = _mm512_shuffle_i64x2(data4, data5, 0xDD);
        
        __m512i even67 = _mm512_shuffle_i64x2(data6, data7, 0x88);
        __m512i odd67 = _mm512_shuffle_i64x2(data6, data7, 0xDD);
        
        // Accumulate
        acc_even[0] = _mm512_xor_si512(acc_even[0], even01);
        acc_even[1] = _mm512_xor_si512(acc_even[1], even23);
        acc_even[2] = _mm512_xor_si512(acc_even[2], even45);
        acc_even[3] = _mm512_xor_si512(acc_even[3], even67);
        
        acc_odd[0] = _mm512_xor_si512(acc_odd[0], odd01);
        acc_odd[1] = _mm512_xor_si512(acc_odd[1], odd23);
        acc_odd[2] = _mm512_xor_si512(acc_odd[2], odd45);
        acc_odd[3] = _mm512_xor_si512(acc_odd[3], odd67);
        
        ptr += 32;
    }
    
    // Handle remaining pairs
    while (ptr + 1 < end) {
        gf128_t even_val = ptr[0];
        gf128_t odd_val = ptr[1];
        
        // Add to first accumulator
        __m128i even_128 = _mm_loadu_si128((const __m128i*)&even_val);
        __m128i odd_128 = _mm_loadu_si128((const __m128i*)&odd_val);
        
        __m512i curr_even = acc_even[0];
        __m512i curr_odd = acc_odd[0];
        
        // Extract first 128 bits, XOR, and put back
        __m128i first_even = _mm512_extracti32x4_epi32(curr_even, 0);
        __m128i first_odd = _mm512_extracti32x4_epi32(curr_odd, 0);
        
        first_even = _mm_xor_si128(first_even, even_128);
        first_odd = _mm_xor_si128(first_odd, odd_128);
        
        acc_even[0] = _mm512_inserti32x4(curr_even, first_even, 0);
        acc_odd[0] = _mm512_inserti32x4(curr_odd, first_odd, 0);
        
        ptr += 2;
    }
    
    // Combine and store accumulators
    for (int i = 0; i < 4; i++) {
        work->accumulators[i] = acc_even[i];
        work->accumulators[i+4] = acc_odd[i];
    }
}

// Final reduction of thread results
static void reduce_thread_results(
    coordinator_t* coord,
    gf128_t* sum_even,
    gf128_t* sum_odd)
{
    *sum_even = gf128_zero();
    *sum_odd = gf128_zero();
    
    // Reduce all thread accumulators
    for (size_t t = 0; t < coord->num_threads; t++) {
        thread_work_t* work = &coord->work[t];
        
        // Reduce even accumulators (first 8)
        for (int i = 0; i < 8; i++) {
            gf128_t temp[4];
            _mm512_storeu_si512(temp, work->accumulators[i]);
            
            for (int j = 0; j < 4; j++) {
                *sum_even = gf128_add(*sum_even, temp[j]);
            }
        }
        
        // Reduce odd accumulators (last 8)
        for (int i = 8; i < 16; i++) {
            gf128_t temp[4];
            _mm512_storeu_si512(temp, work->accumulators[i]);
            
            for (int j = 0; j < 4; j++) {
                *sum_odd = gf128_add(*sum_odd, temp[j]);
            }
        }
    }
}

// Main entry point for optimal sumcheck round
void sumcheck_round_optimal(
    const gf128_t* buffer,
    size_t count,
    gf128_t* sum_even,
    gf128_t* sum_odd,
    int use_separated_layout)
{
    // Determine optimal thread count
    size_t bytes = count * sizeof(gf128_t);
    size_t num_threads = determine_optimal_threads(bytes);
    size_t num_cpus = get_num_cpus();
    
    // Allocate coordinator
    coordinator_t coord;
    coord.num_threads = num_threads;
    coord.work = aligned_alloc(64, num_threads * sizeof(thread_work_t));
    atomic_init(&coord.threads_ready, 0);
    atomic_init(&coord.threads_done, 0);
    
    if (use_separated_layout) {
        // Separate even/odd values first
        separated_buffer_t separated;
        separate_even_odd(buffer, &separated, count);
        
        // Each thread gets a contiguous chunk
        size_t chunk_size = (separated.count + num_threads - 1) / num_threads;
        
        // Launch streaming threads
        #pragma omp parallel num_threads(num_threads)
        {
            int tid = omp_get_thread_num();
            thread_work_t* work = &coord.work[tid];
            
            work->thread_id = tid;
            work->cpu_core = tid % num_cpus;
            work->start_offset = tid * chunk_size;
            work->end_offset = ((tid + 1) * chunk_size < separated.count) ? 
                               (tid + 1) * chunk_size : separated.count;
            
            stream_sumcheck_avx512_separated(
                separated.even_values, 
                separated.odd_values, 
                work);
        }
        
        // Cleanup separated buffers
        free(separated.even_values);
        free(separated.odd_values);
    } else {
        // Use interleaved layout
        size_t chunk_size = (count + num_threads - 1) / num_threads;
        
        // Ensure chunks are aligned to pairs
        chunk_size = (chunk_size + 1) & ~1;
        
        // Launch streaming threads
        #pragma omp parallel num_threads(num_threads)
        {
            int tid = omp_get_thread_num();
            thread_work_t* work = &coord.work[tid];
            
            work->thread_id = tid;
            work->cpu_core = tid % num_cpus;
            work->start_offset = tid * chunk_size;
            work->end_offset = ((tid + 1) * chunk_size < count) ? 
                               (tid + 1) * chunk_size : count;
            
            stream_sumcheck_avx512_interleaved(buffer, work);
        }
    }
    
    // Final reduction
    reduce_thread_results(&coord, sum_even, sum_odd);
    
    // Cleanup
    free(coord.work);
}