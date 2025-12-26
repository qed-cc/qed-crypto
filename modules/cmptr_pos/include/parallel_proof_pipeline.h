/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_PARALLEL_PROOF_PIPELINE_H
#define CMPTR_POS_PARALLEL_PROOF_PIPELINE_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include "basefold_raa.h"
#include "proof_triggers.h"

/* Pipeline stages */
typedef enum {
    STAGE_WITNESS_GEN = 0,
    STAGE_POLYNOMIAL_COMMIT = 1,
    STAGE_SUMCHECK = 2,
    STAGE_MERKLE_BUILD = 3,
    STAGE_FINAL_COMPOSE = 4,
    STAGE_COUNT = 5
} pipeline_stage_type_t;

/* Stage configuration */
typedef struct {
    pipeline_stage_type_t stage;
    uint32_t num_workers;        /* Workers for this stage */
    uint32_t queue_size;         /* Input queue size */
    double expected_time_ms;     /* Expected processing time */
    bool can_parallelize;        /* Can process multiple items */
} stage_config_t;

/* Work item for pipeline */
typedef struct {
    uint64_t id;                 /* Unique work ID */
    consensus_phase_t phase;     /* Which consensus phase */
    void* input_data;            /* Stage input */
    size_t input_size;
    void* output_data;           /* Stage output */
    size_t output_size;
    uint64_t enqueue_time;       /* For latency tracking */
    uint64_t complete_time;
} pipeline_work_t;

/* Worker thread context */
typedef struct {
    uint32_t worker_id;
    pipeline_stage_type_t stage;
    pthread_t thread;
    
    /* Work queue (MPSC) */
    pipeline_work_t** queue;
    uint32_t queue_size;
    uint32_t head;               /* Write position */
    uint32_t tail;               /* Read position */
    pthread_mutex_t queue_lock;
    pthread_cond_t work_available;
    
    /* Statistics */
    uint64_t items_processed;
    uint64_t total_time_us;
    uint64_t idle_time_us;
} pipeline_worker_t;

/* Pipeline stage */
typedef struct pipeline_stage {
    stage_config_t config;
    pipeline_worker_t* workers;
    
    /* Stage function */
    bool (*process)(pipeline_work_t* work, void* context);
    void* context;
    
    /* Connection to next stage */
    struct pipeline_stage* next_stage;
    
    /* Synchronization */
    pthread_mutex_t stats_lock;
    uint64_t total_items;
    uint64_t total_latency_us;
} pipeline_stage_t;

/* Full parallel pipeline */
typedef struct {
    /* Pipeline stages */
    pipeline_stage_t stages[STAGE_COUNT];
    
    /* Global configuration */
    bool enabled;
    uint32_t total_workers;
    
    /* Input queue for first stage */
    pipeline_work_t** input_queue;
    uint32_t input_queue_size;
    uint32_t input_head;
    uint32_t input_tail;
    pthread_mutex_t input_lock;
    pthread_cond_t input_not_full;
    
    /* Output collection */
    void (*on_complete)(pipeline_work_t* work, void* user_data);
    void* user_data;
    
    /* Shutdown control */
    bool shutdown;
    pthread_mutex_t shutdown_lock;
    pthread_cond_t shutdown_complete;
    uint32_t active_workers;
    
    /* Performance metrics */
    uint64_t start_time;
    uint64_t items_submitted;
    uint64_t items_completed;
    double throughput_per_sec;
} parallel_pipeline_t;

/* Pipeline operations */
parallel_pipeline_t* pipeline_create(
    stage_config_t* configs,
    uint32_t num_stages
);

void pipeline_destroy(parallel_pipeline_t* pipeline);

/* Submit work to pipeline */
bool pipeline_submit(
    parallel_pipeline_t* pipeline,
    consensus_phase_t phase,
    void* witness_data,
    size_t witness_size
);

/* Wait for specific work item */
bool pipeline_wait(
    parallel_pipeline_t* pipeline,
    uint64_t work_id,
    uint32_t timeout_ms
);

/* Flush pipeline and wait for completion */
void pipeline_flush(parallel_pipeline_t* pipeline);

/* Get pipeline statistics */
typedef struct {
    /* Per-stage stats */
    struct {
        uint64_t items_processed;
        double avg_latency_ms;
        double utilization_percent;
        uint32_t queue_depth;
    } stages[STAGE_COUNT];
    
    /* Overall stats */
    double total_throughput;
    double end_to_end_latency_ms;
    uint32_t backpressure_events;
    double efficiency_percent;
} pipeline_stats_t;

pipeline_stats_t pipeline_get_stats(parallel_pipeline_t* pipeline);

/* Stage processing functions */
bool stage_witness_generation(pipeline_work_t* work, void* context);
bool stage_polynomial_commit(pipeline_work_t* work, void* context);
bool stage_sumcheck(pipeline_work_t* work, void* context);
bool stage_merkle_build(pipeline_work_t* work, void* context);
bool stage_final_compose(pipeline_work_t* work, void* context);

/* Optimal pipeline configuration */
stage_config_t* get_optimal_pipeline_config(uint32_t num_cores);

#endif /* CMPTR_POS_PARALLEL_PROOF_PIPELINE_H */