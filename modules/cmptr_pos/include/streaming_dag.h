/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_STREAMING_DAG_H
#define CMPTR_POS_STREAMING_DAG_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include "basefold_raa.h"
#include "cmptr_pos_common_types.h"
#include "../../basefold_raa/include/circular_recursion.h"

/* Maximum validators and parents per vertex */
#define MAX_VALIDATORS 10000
#define MAX_PARENTS 100
#define MAX_ROUNDS 100

/* DAG vertex structure */
typedef struct {
    uint32_t round;
    uint32_t author;
    hash256_t parents[MAX_PARENTS];
    uint32_t parent_count;
    signature_t signature;
    uint8_t* payload;
    uint32_t payload_size;
    hash256_t hash;  /* Hash of this vertex */
} dag_vertex_t;

/* DAG round structure */
typedef struct {
    uint32_t round;
    dag_vertex_t* vertices[MAX_VALIDATORS];
    uint32_t vertex_count;
    hash256_t round_hash;  /* Merkle root of round */
    uint64_t timestamp;
} dag_round_t;

/* Round proof using circular recursion */
typedef struct {
    circular_proof_t* proof;      /* Recursive proof of rounds 0..round */
    hash256_t round_commitment;   /* Merkle root of this round */
    uint64_t timestamp;
    uint32_t round;
} dag_round_proof_t;

/* Streaming DAG engine */
typedef struct {
    /* Round storage */
    uint32_t current_round;
    dag_round_t rounds[MAX_ROUNDS];
    dag_round_proof_t round_proofs[MAX_ROUNDS];
    
    /* Streaming configuration */
    bool streaming_enabled;
    bool parallel_proving;
    uint32_t proof_threshold;  /* Start proof at X% vertices */
    
    /* Callbacks */
    void (*on_round_complete)(uint32_t round, dag_round_t* round_data, void* user_data);
    void (*on_round_proven)(uint32_t round, dag_round_proof_t* proof, void* user_data);
    void* callback_data;
    
    /* Parallel proof generation */
    pthread_t proof_threads[4];
    pthread_mutex_t lock;
    pthread_cond_t proof_cond;
    bool stop_threads;
    
    /* Proof queue (simple ring buffer) */
    struct {
        dag_round_t* rounds[16];
        uint32_t head;
        uint32_t tail;
        pthread_mutex_t lock;
        pthread_cond_t not_empty;
        pthread_cond_t not_full;
    } proof_queue;
    
    /* Performance metrics */
    uint64_t total_proof_time_us;
    uint32_t proofs_generated;
    uint64_t total_vertices;
} streaming_dag_engine_t;

/* Initialize streaming DAG engine */
streaming_dag_engine_t* streaming_dag_init(bool enable_streaming, bool parallel_proving);

/* Free streaming DAG engine */
void streaming_dag_free(streaming_dag_engine_t* engine);

/* Add vertex to current round */
bool streaming_dag_add_vertex(
    streaming_dag_engine_t* engine,
    dag_vertex_t* vertex
);

/* Complete current round and start next */
bool streaming_dag_complete_round(streaming_dag_engine_t* engine);

/* Get proof for specific round */
dag_round_proof_t* streaming_dag_get_proof(
    streaming_dag_engine_t* engine,
    uint32_t round
);

/* Verify streaming proof up to round */
bool streaming_dag_verify_proof(
    dag_round_proof_t* proof,
    hash256_t genesis_hash
);

/* Light client update */
typedef struct {
    uint32_t tracked_round;
    dag_round_proof_t latest_proof;
    hash256_t genesis_hash;
} dag_light_client_t;

bool dag_light_client_update(
    dag_light_client_t* client,
    dag_round_proof_t* new_proof
);

/* Performance statistics */
typedef struct {
    double avg_proof_time_ms;
    double throughput_vertices_per_sec;
    uint32_t rounds_proven;
    uint64_t total_vertices;
    double compression_ratio;  /* Original size / proof size */
} streaming_dag_stats_t;

streaming_dag_stats_t streaming_dag_get_stats(streaming_dag_engine_t* engine);

/* Utility functions */
hash256_t compute_vertex_hash(dag_vertex_t* vertex);
hash256_t compute_round_merkle_root(dag_round_t* round);
bool verify_vertex_signature(dag_vertex_t* vertex);
bool validate_round_structure(dag_round_t* round);

#endif /* CMPTR_POS_STREAMING_DAG_H */