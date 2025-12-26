/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "streaming_dag.h"
#include "circular_recursion.h"
#include "basefold_raa_wrapper.h"
#include "sha3.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <time.h>

/* Internal vertex storage with chain links */
typedef struct vertex_chain {
    dag_vertex_t vertex;
    struct vertex_chain* next;
    uint32_t ref_count;
} vertex_chain_t;

/* Hash map bucket for vertex lookup */
typedef struct vertex_bucket {
    vertex_chain_t* head;
    pthread_rwlock_t lock;
} vertex_bucket_t;

/* Real streaming DAG implementation */
struct streaming_dag_engine {
    /* Configuration */
    dag_config_t config;
    
    /* Vertex storage - hash map with chaining */
    vertex_bucket_t* buckets;
    uint32_t num_buckets;
    uint32_t vertex_count;
    
    /* Round management */
    uint32_t current_round;
    uint32_t finalized_round;
    pthread_mutex_t round_lock;
    
    /* Circular recursion state */
    circular_recursion_t* circular;
    circular_proof_t* current_proof;
    pthread_mutex_t proof_lock;
    
    /* Round proofs */
    dag_round_proof_t* round_proofs;
    uint32_t proof_capacity;
    pthread_rwlock_t proofs_lock;
    
    /* Worker threads for proof generation */
    pthread_t* proof_workers;
    uint32_t num_workers;
    bool workers_running;
    
    /* Work queue for proof generation */
    struct {
        dag_vertex_t** vertices;
        uint32_t* counts;
        uint32_t head;
        uint32_t tail;
        uint32_t capacity;
        pthread_mutex_t lock;
        pthread_cond_t not_empty;
        pthread_cond_t not_full;
    } work_queue;
    
    /* Statistics */
    uint64_t vertices_added;
    uint64_t proofs_generated;
    uint64_t total_proof_time_ms;
};

/* Hash function for vertex lookup */
static uint32_t vertex_hash(hash256_t* hash, uint32_t num_buckets) {
    uint32_t h = 0;
    for (int i = 0; i < 8; i++) {
        h ^= ((uint32_t*)hash->bytes)[i];
    }
    return h % num_buckets;
}

/* Worker thread for proof generation */
static void* proof_worker_thread(void* arg) {
    streaming_dag_engine_t* dag = (streaming_dag_engine_t*)arg;
    
    while (dag->workers_running) {
        /* Get work from queue */
        pthread_mutex_lock(&dag->work_queue.lock);
        
        while (dag->work_queue.head == dag->work_queue.tail && dag->workers_running) {
            pthread_cond_wait(&dag->work_queue.not_empty, &dag->work_queue.lock);
        }
        
        if (!dag->workers_running) {
            pthread_mutex_unlock(&dag->work_queue.lock);
            break;
        }
        
        /* Get vertices for this round */
        dag_vertex_t* vertices = dag->work_queue.vertices[dag->work_queue.tail];
        uint32_t count = dag->work_queue.counts[dag->work_queue.tail];
        uint32_t round = vertices[0].round; /* All vertices in same round */
        
        dag->work_queue.tail = (dag->work_queue.tail + 1) % dag->work_queue.capacity;
        pthread_cond_signal(&dag->work_queue.not_full);
        pthread_mutex_unlock(&dag->work_queue.lock);
        
        /* Generate proof for this round */
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        /* Create witness from vertices */
        size_t witness_size = count * sizeof(dag_vertex_t);
        uint8_t* witness = malloc(witness_size);
        memcpy(witness, vertices, witness_size);
        
        /* Generate recursive proof */
        pthread_mutex_lock(&dag->proof_lock);
        
        if (dag->config.enable_circular_recursion && dag->circular) {
            /* Use circular recursion to maintain constant proof size */
            blockchain_state_t state1 = {
                .height = round,
                .hash = vertices[0].hash,
                .timestamp = vertices[0].timestamp
            };
            
            blockchain_state_t state2 = {
                .height = round,
                .hash = vertices[count-1].hash,
                .timestamp = vertices[count-1].timestamp
            };
            
            /* Generate new proof combining with previous */
            circular_proof_t* new_proof = circular_recursion_prove(
                dag->circular,
                dag->current_proof,
                &state1,
                &state2
            );
            
            if (new_proof) {
                /* Free old proof and update */
                if (dag->current_proof && dag->current_proof != new_proof) {
                    circular_recursion_free_proof(dag->current_proof);
                }
                dag->current_proof = new_proof;
                
                /* Store round proof */
                pthread_rwlock_wrlock(&dag->proofs_lock);
                
                if (round < dag->proof_capacity) {
                    dag->round_proofs[round].proof = new_proof;
                    dag->round_proofs[round].round = round;
                    dag->round_proofs[round].timestamp = vertices[0].timestamp;
                    
                    /* Compute round commitment */
                    sha3_ctx_t ctx;
                    sha3_256_init(&ctx);
                    for (uint32_t i = 0; i < count; i++) {
                        sha3_256_update(&ctx, (uint8_t*)&vertices[i], sizeof(dag_vertex_t));
                    }
                    sha3_256_final(&ctx, dag->round_proofs[round].round_commitment.bytes);
                }
                
                pthread_rwlock_unlock(&dag->proofs_lock);
                dag->proofs_generated++;
            }
        } else {
            /* Fallback to standard proof generation */
            basefold_raa_proof_t* proof = basefold_raa_prove_simple(
                witness, witness_size, 20, 1000
            );
            
            if (proof) {
                /* Wrap in circular proof structure */
                circular_proof_t* c_proof = calloc(1, sizeof(circular_proof_t));
                c_proof->current_proof = proof;
                c_proof->proof_size = proof->proof_size;
                
                if (dag->current_proof) {
                    circular_recursion_free_proof(dag->current_proof);
                }
                dag->current_proof = c_proof;
                
                /* Store round proof */
                pthread_rwlock_wrlock(&dag->proofs_lock);
                if (round < dag->proof_capacity) {
                    dag->round_proofs[round].proof = c_proof;
                    dag->round_proofs[round].round = round;
                }
                pthread_rwlock_unlock(&dag->proofs_lock);
            }
        }
        
        pthread_mutex_unlock(&dag->proof_lock);
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        uint64_t elapsed_ms = (end.tv_sec - start.tv_sec) * 1000 + 
                              (end.tv_nsec - start.tv_nsec) / 1000000;
        dag->total_proof_time_ms += elapsed_ms;
        
        /* Clean up */
        free(witness);
        free(vertices);
    }
    
    return NULL;
}

/* Create streaming DAG engine */
streaming_dag_engine_t* streaming_dag_create(dag_config_t* config) {
    streaming_dag_engine_t* dag = calloc(1, sizeof(streaming_dag_engine_t));
    if (!dag) return NULL;
    
    dag->config = *config;
    
    /* Initialize vertex storage */
    dag->num_buckets = 1024;
    dag->buckets = calloc(dag->num_buckets, sizeof(vertex_bucket_t));
    for (uint32_t i = 0; i < dag->num_buckets; i++) {
        pthread_rwlock_init(&dag->buckets[i].lock, NULL);
    }
    
    /* Initialize round management */
    pthread_mutex_init(&dag->round_lock, NULL);
    pthread_mutex_init(&dag->proof_lock, NULL);
    
    /* Initialize circular recursion if enabled */
    if (config->enable_circular_recursion) {
        circular_config_t circ_config = {
            .max_depth = 30,
            .proof_size_limit = 200 * 1024,
            .enable_compression = true,
            .cache_proofs = true
        };
        dag->circular = circular_recursion_init(&circ_config);
    }
    
    /* Initialize round proofs storage */
    dag->proof_capacity = 1000;
    dag->round_proofs = calloc(dag->proof_capacity, sizeof(dag_round_proof_t));
    pthread_rwlock_init(&dag->proofs_lock, NULL);
    
    /* Initialize work queue */
    dag->work_queue.capacity = 32;
    dag->work_queue.vertices = calloc(dag->work_queue.capacity, sizeof(dag_vertex_t*));
    dag->work_queue.counts = calloc(dag->work_queue.capacity, sizeof(uint32_t));
    pthread_mutex_init(&dag->work_queue.lock, NULL);
    pthread_cond_init(&dag->work_queue.not_empty, NULL);
    pthread_cond_init(&dag->work_queue.not_full, NULL);
    
    /* Start worker threads */
    dag->num_workers = config->proof_workers;
    dag->proof_workers = calloc(dag->num_workers, sizeof(pthread_t));
    dag->workers_running = true;
    
    for (uint32_t i = 0; i < dag->num_workers; i++) {
        pthread_create(&dag->proof_workers[i], NULL, proof_worker_thread, dag);
    }
    
    return dag;
}

/* Destroy streaming DAG engine */
void streaming_dag_destroy(streaming_dag_engine_t* dag) {
    if (!dag) return;
    
    /* Stop workers */
    dag->workers_running = false;
    pthread_cond_broadcast(&dag->work_queue.not_empty);
    
    for (uint32_t i = 0; i < dag->num_workers; i++) {
        pthread_join(dag->proof_workers[i], NULL);
    }
    free(dag->proof_workers);
    
    /* Free vertex storage */
    for (uint32_t i = 0; i < dag->num_buckets; i++) {
        vertex_chain_t* curr = dag->buckets[i].head;
        while (curr) {
            vertex_chain_t* next = curr->next;
            free(curr);
            curr = next;
        }
        pthread_rwlock_destroy(&dag->buckets[i].lock);
    }
    free(dag->buckets);
    
    /* Free proofs */
    if (dag->current_proof) {
        circular_recursion_free_proof(dag->current_proof);
    }
    free(dag->round_proofs);
    
    /* Free circular recursion */
    if (dag->circular) {
        circular_recursion_destroy(dag->circular);
    }
    
    /* Free work queue */
    free(dag->work_queue.vertices);
    free(dag->work_queue.counts);
    pthread_mutex_destroy(&dag->work_queue.lock);
    pthread_cond_destroy(&dag->work_queue.not_empty);
    pthread_cond_destroy(&dag->work_queue.not_full);
    
    /* Destroy locks */
    pthread_mutex_destroy(&dag->round_lock);
    pthread_mutex_destroy(&dag->proof_lock);
    pthread_rwlock_destroy(&dag->proofs_lock);
    
    free(dag);
}

/* Add vertex to DAG */
bool streaming_dag_add_vertex(streaming_dag_engine_t* dag, dag_vertex_t* vertex) {
    if (!dag || !vertex) return false;
    
    /* Get bucket for this vertex */
    uint32_t bucket_idx = vertex_hash(&vertex->hash, dag->num_buckets);
    vertex_bucket_t* bucket = &dag->buckets[bucket_idx];
    
    /* Create new vertex chain node */
    vertex_chain_t* node = calloc(1, sizeof(vertex_chain_t));
    node->vertex = *vertex;
    node->ref_count = 1;
    
    /* Add to bucket */
    pthread_rwlock_wrlock(&bucket->lock);
    
    /* Check if vertex already exists */
    vertex_chain_t* curr = bucket->head;
    while (curr) {
        if (memcmp(&curr->vertex.hash, &vertex->hash, sizeof(hash256_t)) == 0) {
            pthread_rwlock_unlock(&bucket->lock);
            free(node);
            return false; /* Duplicate vertex */
        }
        curr = curr->next;
    }
    
    /* Add to head of chain */
    node->next = bucket->head;
    bucket->head = node;
    dag->vertex_count++;
    dag->vertices_added++;
    
    pthread_rwlock_unlock(&bucket->lock);
    
    return true;
}

/* Get vertex by hash */
dag_vertex_t* streaming_dag_get_vertex(streaming_dag_engine_t* dag, hash256_t hash) {
    if (!dag) return NULL;
    
    uint32_t bucket_idx = vertex_hash(&hash, dag->num_buckets);
    vertex_bucket_t* bucket = &dag->buckets[bucket_idx];
    
    pthread_rwlock_rdlock(&bucket->lock);
    
    vertex_chain_t* curr = bucket->head;
    while (curr) {
        if (memcmp(&curr->vertex.hash, &hash, sizeof(hash256_t)) == 0) {
            pthread_rwlock_unlock(&bucket->lock);
            return &curr->vertex;
        }
        curr = curr->next;
    }
    
    pthread_rwlock_unlock(&bucket->lock);
    return NULL;
}

/* Start new round */
void streaming_dag_start_round(streaming_dag_engine_t* dag, uint32_t round) {
    pthread_mutex_lock(&dag->round_lock);
    dag->current_round = round;
    pthread_mutex_unlock(&dag->round_lock);
}

/* Finalize round and trigger proof generation */
void streaming_dag_finalize_round(streaming_dag_engine_t* dag, uint32_t round) {
    /* Collect all vertices from this round */
    dag_vertex_t* round_vertices = malloc(dag->config.max_round_size * sizeof(dag_vertex_t));
    uint32_t count = 0;
    
    /* Scan all buckets for vertices in this round */
    for (uint32_t i = 0; i < dag->num_buckets; i++) {
        pthread_rwlock_rdlock(&dag->buckets[i].lock);
        
        vertex_chain_t* curr = dag->buckets[i].head;
        while (curr && count < dag->config.max_round_size) {
            if (curr->vertex.round == round) {
                round_vertices[count++] = curr->vertex;
            }
            curr = curr->next;
        }
        
        pthread_rwlock_unlock(&dag->buckets[i].lock);
    }
    
    if (count > 0) {
        /* Submit to work queue for proof generation */
        pthread_mutex_lock(&dag->work_queue.lock);
        
        /* Wait if queue is full */
        while ((dag->work_queue.head + 1) % dag->work_queue.capacity == dag->work_queue.tail) {
            pthread_cond_wait(&dag->work_queue.not_full, &dag->work_queue.lock);
        }
        
        /* Add work item */
        dag->work_queue.vertices[dag->work_queue.head] = round_vertices;
        dag->work_queue.counts[dag->work_queue.head] = count;
        dag->work_queue.head = (dag->work_queue.head + 1) % dag->work_queue.capacity;
        
        pthread_cond_signal(&dag->work_queue.not_empty);
        pthread_mutex_unlock(&dag->work_queue.lock);
    } else {
        free(round_vertices);
    }
    
    /* Update finalized round */
    pthread_mutex_lock(&dag->round_lock);
    if (round > dag->finalized_round) {
        dag->finalized_round = round;
    }
    pthread_mutex_unlock(&dag->round_lock);
}

/* Get proof for round */
dag_round_proof_t* streaming_dag_get_proof(streaming_dag_engine_t* dag, uint32_t round) {
    if (!dag || round >= dag->proof_capacity) return NULL;
    
    pthread_rwlock_rdlock(&dag->proofs_lock);
    dag_round_proof_t* proof = NULL;
    
    if (dag->round_proofs[round].proof != NULL) {
        proof = &dag->round_proofs[round];
    }
    
    pthread_rwlock_unlock(&dag->proofs_lock);
    return proof;
}

/* Get current cumulative proof */
circular_proof_t* streaming_dag_get_cumulative_proof(streaming_dag_engine_t* dag) {
    if (!dag) return NULL;
    
    pthread_mutex_lock(&dag->proof_lock);
    circular_proof_t* proof = dag->current_proof;
    pthread_mutex_unlock(&dag->proof_lock);
    
    return proof;
}

/* Get statistics */
dag_stats_t streaming_dag_get_stats(streaming_dag_engine_t* dag) {
    dag_stats_t stats = {0};
    
    if (!dag) return stats;
    
    pthread_mutex_lock(&dag->round_lock);
    stats.current_round = dag->current_round;
    stats.finalized_round = dag->finalized_round;
    pthread_mutex_unlock(&dag->round_lock);
    
    stats.total_vertices = dag->vertices_added;
    stats.active_vertices = dag->vertex_count;
    stats.rounds_proven = dag->proofs_generated;
    
    if (dag->proofs_generated > 0) {
        stats.avg_proof_time_ms = (double)dag->total_proof_time_ms / dag->proofs_generated;
    }
    
    pthread_mutex_lock(&dag->proof_lock);
    if (dag->current_proof) {
        stats.cumulative_proof_size_kb = dag->current_proof->proof_size / 1024.0;
    }
    pthread_mutex_unlock(&dag->proof_lock);
    
    stats.memory_usage_mb = (dag->vertex_count * sizeof(vertex_chain_t) + 
                            dag->proof_capacity * sizeof(dag_round_proof_t)) / (1024.0 * 1024.0);
    
    return stats;
}