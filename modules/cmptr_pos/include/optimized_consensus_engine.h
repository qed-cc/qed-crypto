/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_OPTIMIZED_CONSENSUS_ENGINE_H
#define CMPTR_POS_OPTIMIZED_CONSENSUS_ENGINE_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include "cmptr_pos.h"
#include "proof_triggers.h"
#include "streaming_dag.h"
#include "hierarchical_vrf.h"
#include "parallel_proof_pipeline.h"
#include "early_finality.h"

/* Optimized consensus configuration */
typedef struct {
    /* Base configuration */
    pos_config_t base_config;
    
    /* Optimization flags */
    bool enable_proof_triggers;
    bool enable_streaming_dag;
    bool enable_hierarchical_vrf;
    bool enable_parallel_pipeline;
    bool enable_early_finality;
    
    /* Performance targets */
    uint32_t target_consensus_ms;    /* Target time per round */
    uint32_t max_proof_size_kb;      /* Maximum proof size */
    double efficiency_threshold;     /* Min efficiency required */
} optimized_config_t;

/* Integrated consensus engine */
typedef struct {
    /* Base PoS state */
    pos_state_t* pos_state;
    
    /* Optimization components */
    trigger_engine_t* triggers;
    streaming_dag_engine_t* dag;
    vrf_tree_t* vrf_tree;
    parallel_pipeline_t* pipeline;
    early_finality_engine_t* finality;
    
    /* Configuration */
    optimized_config_t config;
    
    /* Consensus state */
    uint32_t current_epoch;
    uint32_t current_round;
    consensus_phase_t current_phase;
    
    /* Performance tracking */
    struct {
        uint64_t rounds_completed;
        uint64_t total_time_ms;
        uint64_t phase_times_ms[PHASE_COUNT];
        uint64_t proof_generation_ms;
        uint64_t finality_time_ms;
    } metrics;
    
    /* Thread management */
    pthread_t consensus_thread;
    bool running;
    pthread_mutex_t state_lock;
    
    /* Callbacks */
    void (*on_round_complete)(uint32_t round, void* user_data);
    void (*on_finality)(uint32_t round, finality_type_t type, void* user_data);
    void* callback_data;
} optimized_consensus_engine_t;

/* Engine lifecycle */
optimized_consensus_engine_t* optimized_consensus_create(
    optimized_config_t* config,
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain
);

void optimized_consensus_destroy(optimized_consensus_engine_t* engine);

/* Start/stop consensus */
bool optimized_consensus_start(optimized_consensus_engine_t* engine);
void optimized_consensus_stop(optimized_consensus_engine_t* engine);

/* Run single consensus round */
bool optimized_consensus_run_round(optimized_consensus_engine_t* engine);

/* Query state */
typedef struct {
    uint32_t current_round;
    uint32_t finalized_round;
    consensus_phase_t current_phase;
    
    /* Performance metrics */
    double avg_round_time_ms;
    double avg_proof_time_ms;
    double avg_finality_time_ms;
    
    /* Optimization impact */
    double speedup_vs_baseline;
    double proof_size_reduction;
    double memory_reduction;
    
    /* Component stats */
    trigger_stats_t trigger_stats;
    dag_stats_t dag_stats;
    vrf_stats_t vrf_stats;
    pipeline_stats_t pipeline_stats;
    finality_stats_t finality_stats;
} consensus_stats_t;

consensus_stats_t optimized_consensus_get_stats(optimized_consensus_engine_t* engine);

/* Force checkpoint creation */
bool optimized_consensus_checkpoint(
    optimized_consensus_engine_t* engine,
    uint32_t round
);

/* Get proof for light clients */
basefold_raa_proof_t* optimized_consensus_get_proof(
    optimized_consensus_engine_t* engine,
    uint32_t round
);

/* Benchmark utilities */
typedef struct {
    uint32_t num_rounds;
    uint32_t num_validators;
    uint32_t transactions_per_round;
    bool enable_all_optimizations;
    bool detailed_metrics;
} benchmark_config_t;

typedef struct {
    /* Timing */
    double baseline_time_ms;
    double optimized_time_ms;
    double speedup_factor;
    
    /* Resource usage */
    uint64_t baseline_memory_mb;
    uint64_t optimized_memory_mb;
    double memory_reduction;
    
    /* Proof metrics */
    uint32_t baseline_proof_size_kb;
    uint32_t optimized_proof_size_kb;
    double size_reduction;
    
    /* Per-optimization impact */
    struct {
        const char* name;
        double time_saved_ms;
        double contribution_percent;
    } optimizations[5];
} benchmark_results_t;

benchmark_results_t optimized_consensus_benchmark(
    benchmark_config_t* config
);

#endif /* CMPTR_POS_OPTIMIZED_CONSENSUS_ENGINE_H */