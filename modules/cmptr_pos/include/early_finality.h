/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_EARLY_FINALITY_H
#define CMPTR_POS_EARLY_FINALITY_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include "streaming_dag.h"
#include "basefold_raa.h"
#include "cmptr_pos_common_types.h"

/* Finality configuration */
typedef struct {
    /* Probabilistic finality */
    uint32_t k_deep;             /* Rounds for probabilistic finality */
    double reversal_threshold;   /* Max acceptable reversal probability */
    
    /* Economic finality */
    double stake_threshold;      /* Fraction of stake required (e.g., 0.67) */
    uint64_t min_stake_amount;   /* Minimum absolute stake */
    
    /* Timing */
    uint32_t check_interval_ms;  /* How often to check finality */
    uint32_t max_wait_ms;        /* Maximum wait for finality */
    
    /* Slashing */
    bool enable_slashing;        /* Slash for finality violations */
    uint64_t slash_amount;       /* Amount to slash */
} finality_config_t;

/* Vertex finality status */
typedef struct {
    hash256_t vertex_hash;
    uint32_t round;
    finality_type_t finality_type;
    uint64_t finalized_at;       /* Timestamp when finalized */
    
    /* Support data */
    uint64_t supporting_stake;   /* Stake supporting this vertex */
    uint32_t confirming_rounds;  /* Rounds since vertex */
    double reversal_probability; /* Calculated reversal probability */
    
    /* Certificate (if available) */
    basefold_raa_proof_t* finality_proof;
} vertex_finality_t;

/* Finality checkpoint */
typedef struct {
    uint32_t round;
    hash256_t dag_root;
    uint64_t timestamp;
    finality_type_t type;
    
    /* Validators who signed */
    uint32_t* signers;
    uint32_t signer_count;
    uint64_t total_stake;
    
    /* Checkpoint proof */
    basefold_raa_proof_t* checkpoint_proof;
} finality_checkpoint_t;

/* Early finality engine */
typedef struct {
    /* Configuration */
    finality_config_t config;
    
    /* DAG tracking */
    streaming_dag_engine_t* dag;
    uint32_t latest_round;
    uint32_t finalized_round;
    
    /* Vertex tracking (hash map) */
    struct {
        vertex_finality_t** buckets;
        uint32_t num_buckets;
        uint32_t count;
        pthread_rwlock_t lock;
    } vertices;
    
    /* Checkpoints */
    finality_checkpoint_t* checkpoints;
    uint32_t checkpoint_count;
    uint32_t checkpoint_capacity;
    pthread_mutex_t checkpoint_lock;
    
    /* Stake tracking */
    struct {
        uint64_t total_stake;
        uint64_t* validator_stakes;
        uint32_t validator_count;
    } stake_info;
    
    /* Worker thread */
    pthread_t finality_thread;
    bool running;
    
    /* Callbacks */
    void (*on_vertex_finalized)(hash256_t vertex, finality_type_t type, void* user_data);
    void (*on_checkpoint_created)(finality_checkpoint_t* checkpoint, void* user_data);
    void* callback_data;
    
    /* Statistics */
    uint64_t vertices_finalized;
    uint64_t checkpoints_created;
    uint64_t avg_finality_time_ms;
    uint64_t slashing_events;
} early_finality_engine_t;

/* Engine operations */
early_finality_engine_t* early_finality_create(
    finality_config_t* config,
    streaming_dag_engine_t* dag
);

void early_finality_destroy(early_finality_engine_t* engine);

/* Start/stop finality checking */
bool early_finality_start(early_finality_engine_t* engine);
void early_finality_stop(early_finality_engine_t* engine);

/* Update stake information */
void early_finality_update_stake(
    early_finality_engine_t* engine,
    uint32_t validator_id,
    uint64_t stake_amount
);

/* Submit vertex for finality tracking */
void early_finality_track_vertex(
    early_finality_engine_t* engine,
    dag_vertex_t* vertex,
    uint64_t* supporting_stakes,  /* Stake amounts of validators who built on this */
    uint32_t support_count
);

/* Query finality status */
vertex_finality_t* early_finality_get_status(
    early_finality_engine_t* engine,
    hash256_t vertex_hash
);

/* Get latest finalized round */
uint32_t early_finality_get_finalized_round(early_finality_engine_t* engine);

/* Get checkpoint by round */
finality_checkpoint_t* early_finality_get_checkpoint(
    early_finality_engine_t* engine,
    uint32_t round
);

/* Force checkpoint creation */
bool early_finality_create_checkpoint(
    early_finality_engine_t* engine,
    uint32_t round
);

/* Slashing detection */
typedef struct {
    uint32_t validator_id;
    hash256_t vertex1;
    hash256_t vertex2;
    uint32_t round;
    uint64_t evidence_timestamp;
} slashing_evidence_t;

slashing_evidence_t* early_finality_detect_violation(
    early_finality_engine_t* engine,
    dag_vertex_t* vertex
);

/* Statistics */
typedef struct {
    uint64_t total_vertices_tracked;
    uint64_t vertices_finalized;
    uint32_t finalized_round;
    uint32_t pending_vertices;
    
    /* Finality times */
    double avg_probabilistic_time_ms;
    double avg_economic_time_ms;
    double avg_absolute_time_ms;
    
    /* Checkpoint info */
    uint32_t checkpoint_count;
    uint32_t checkpoint_interval;
    
    /* Slashing */
    uint64_t slashing_events;
    uint64_t total_slashed;
} finality_stats_t;

finality_stats_t early_finality_get_stats(early_finality_engine_t* engine);

/* Finality calculations */
double calculate_reversal_probability(
    uint32_t k_deep,
    double byzantine_fraction
);

uint64_t calculate_economic_threshold(
    uint64_t total_stake,
    double threshold_fraction
);

#endif /* CMPTR_POS_EARLY_FINALITY_H */