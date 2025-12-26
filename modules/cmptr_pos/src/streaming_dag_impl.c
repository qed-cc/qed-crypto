/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "streaming_dag.h"
#include "sha3.h"
#include "circular_recursion.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>

/* Get current time in microseconds */
static uint64_t get_time_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

/* Compute hash of vertex */
hash256_t compute_vertex_hash(dag_vertex_t* vertex) {
    sha3_ctx_t ctx;
    hash256_t hash;
    
    sha3_256_init(&ctx);
    sha3_update(&ctx, &vertex->round, sizeof(vertex->round));
    sha3_update(&ctx, &vertex->author, sizeof(vertex->author));
    
    for (uint32_t i = 0; i < vertex->parent_count; i++) {
        sha3_update(&ctx, &vertex->parents[i], sizeof(hash256_t));
    }
    
    if (vertex->payload && vertex->payload_size > 0) {
        sha3_update(&ctx, vertex->payload, vertex->payload_size);
    }
    
    sha3_final(&ctx, hash.bytes);
    return hash;
}

/* Compute Merkle root of round */
hash256_t compute_round_merkle_root(dag_round_t* round) {
    if (round->vertex_count == 0) {
        return (hash256_t){0};
    }
    
    /* Simple Merkle tree construction */
    hash256_t* hashes = calloc(round->vertex_count, sizeof(hash256_t));
    
    /* Leaf level: vertex hashes */
    for (uint32_t i = 0; i < round->vertex_count; i++) {
        hashes[i] = round->vertices[i]->hash;
    }
    
    /* Build tree bottom-up */
    uint32_t level_size = round->vertex_count;
    while (level_size > 1) {
        uint32_t next_level_size = (level_size + 1) / 2;
        
        for (uint32_t i = 0; i < next_level_size; i++) {
            sha3_ctx_t ctx;
            sha3_256_init(&ctx);
            
            sha3_update(&ctx, &hashes[i * 2], sizeof(hash256_t));
            if (i * 2 + 1 < level_size) {
                sha3_update(&ctx, &hashes[i * 2 + 1], sizeof(hash256_t));
            }
            
            sha3_final(&ctx, hashes[i].bytes);
        }
        
        level_size = next_level_size;
    }
    
    hash256_t root = hashes[0];
    free(hashes);
    return root;
}

/* Verify vertex signature (placeholder - would use actual crypto) */
bool verify_vertex_signature(dag_vertex_t* vertex) {
    /* In production, verify signature against author's public key */
    /* For now, check signature is non-zero */
    for (int i = 0; i < 64; i++) {
        if (vertex->signature.bytes[i] != 0) return true;
    }
    return false;
}

/* Validate round structure */
bool validate_round_structure(dag_round_t* round) {
    if (round->vertex_count == 0) return false;
    
    /* Check each vertex */
    for (uint32_t i = 0; i < round->vertex_count; i++) {
        dag_vertex_t* v = round->vertices[i];
        
        /* Verify round number */
        if (v->round != round->round) return false;
        
        /* Verify signature */
        if (!verify_vertex_signature(v)) return false;
        
        /* Verify parent count (need 2f+1 for Byzantine consensus) */
        uint32_t min_parents = (round->round == 0) ? 0 : (MAX_VALIDATORS * 2 / 3);
        if (v->parent_count < min_parents) return false;
    }
    
    return true;
}

/* Proof generation worker thread */
static void* proof_worker_thread(void* arg) {
    streaming_dag_engine_t* engine = (streaming_dag_engine_t*)arg;
    
    while (true) {
        /* Wait for work */
        pthread_mutex_lock(&engine->proof_queue.lock);
        
        while (engine->proof_queue.head == engine->proof_queue.tail && !engine->stop_threads) {
            pthread_cond_wait(&engine->proof_queue.not_empty, &engine->proof_queue.lock);
        }
        
        if (engine->stop_threads) {
            pthread_mutex_unlock(&engine->proof_queue.lock);
            break;
        }
        
        /* Get round to prove */
        dag_round_t* round = engine->proof_queue.rounds[engine->proof_queue.tail];
        engine->proof_queue.tail = (engine->proof_queue.tail + 1) % 16;
        pthread_cond_signal(&engine->proof_queue.not_full);
        pthread_mutex_unlock(&engine->proof_queue.lock);
        
        /* Generate proof */
        uint64_t start = get_time_us();
        
        /* Create witness for this round */
        struct {
            uint32_t round;
            hash256_t round_hash;
            uint32_t vertex_count;
            bool signatures_valid;
            hash256_t parent_commitments[MAX_VALIDATORS];
        } witness;
        
        witness.round = round->round;
        witness.round_hash = round->round_hash;
        witness.vertex_count = round->vertex_count;
        witness.signatures_valid = true;
        
        /* Verify all signatures and collect parent commitments */
        for (uint32_t i = 0; i < round->vertex_count; i++) {
            if (!verify_vertex_signature(round->vertices[i])) {
                witness.signatures_valid = false;
            }
            /* In real implementation, would compute parent commitments */
        }
        
        /* Get previous proof for circular recursion */
        circular_proof_t* prev_proof = NULL;
        if (round->round > 0) {
            pthread_mutex_lock(&engine->lock);
            if (engine->round_proofs[round->round - 1].proof) {
                prev_proof = engine->round_proofs[round->round - 1].proof;
            }
            pthread_mutex_unlock(&engine->lock);
        }
        
        /* Generate circular recursive proof */
        blockchain_state_t prev_state = {0};
        blockchain_state_t new_state = {0};
        
        /* Set up states for circular recursion */
        memcpy(new_state.state_hash, witness.round_hash.bytes, 32);
        new_state.block_number = round->round;
        new_state.accumulated_work = round->round; /* Simplified */
        
        if (prev_proof) {
            /* Get previous state from somewhere - simplified for now */
            prev_state.block_number = round->round - 1;
        }
        
        circular_proof_t* proof = basefold_raa_circular_prove(
            &prev_state,
            &new_state,
            prev_proof,
            round->round == 0  /* is_genesis */
        );
        
        uint64_t end = get_time_us();
        
        /* Store proof */
        pthread_mutex_lock(&engine->lock);
        engine->round_proofs[round->round].proof = proof;
        engine->round_proofs[round->round].round_commitment = round->round_hash;
        engine->round_proofs[round->round].timestamp = end;
        engine->round_proofs[round->round].round = round->round;
        
        engine->total_proof_time_us += (end - start);
        engine->proofs_generated++;
        
        /* Notify callback */
        if (engine->on_round_proven) {
            engine->on_round_proven(
                round->round,
                &engine->round_proofs[round->round],
                engine->callback_data
            );
        }
        
        pthread_mutex_unlock(&engine->lock);
    }
    
    return NULL;
}

/* Initialize streaming DAG engine */
streaming_dag_engine_t* streaming_dag_init(bool enable_streaming, bool parallel_proving) {
    streaming_dag_engine_t* engine = calloc(1, sizeof(*engine));
    if (!engine) return NULL;
    
    engine->streaming_enabled = enable_streaming;
    engine->parallel_proving = parallel_proving;
    engine->proof_threshold = 80;  /* Start proof at 80% vertices */
    
    /* Initialize synchronization */
    pthread_mutex_init(&engine->lock, NULL);
    pthread_cond_init(&engine->proof_cond, NULL);
    
    pthread_mutex_init(&engine->proof_queue.lock, NULL);
    pthread_cond_init(&engine->proof_queue.not_empty, NULL);
    pthread_cond_init(&engine->proof_queue.not_full, NULL);
    
    /* Start proof worker threads if parallel proving */
    if (parallel_proving) {
        int num_threads = enable_streaming ? 4 : 1;
        for (int i = 0; i < num_threads; i++) {
            pthread_create(&engine->proof_threads[i], NULL, proof_worker_thread, engine);
        }
    }
    
    return engine;
}

/* Free streaming DAG engine */
void streaming_dag_free(streaming_dag_engine_t* engine) {
    if (!engine) return;
    
    /* Stop worker threads */
    if (engine->parallel_proving) {
        pthread_mutex_lock(&engine->proof_queue.lock);
        engine->stop_threads = true;
        pthread_cond_broadcast(&engine->proof_queue.not_empty);
        pthread_mutex_unlock(&engine->proof_queue.lock);
        
        for (int i = 0; i < 4; i++) {
            if (engine->proof_threads[i]) {
                pthread_join(engine->proof_threads[i], NULL);
            }
        }
    }
    
    /* Free proofs */
    for (uint32_t i = 0; i < MAX_ROUNDS; i++) {
        if (engine->round_proofs[i].proof) {
            basefold_raa_proof_free(engine->round_proofs[i].proof);
        }
    }
    
    /* Free rounds and vertices */
    for (uint32_t r = 0; r < engine->current_round; r++) {
        for (uint32_t v = 0; v < engine->rounds[r].vertex_count; v++) {
            free(engine->rounds[r].vertices[v]);
        }
    }
    
    /* Destroy synchronization */
    pthread_mutex_destroy(&engine->lock);
    pthread_cond_destroy(&engine->proof_cond);
    pthread_mutex_destroy(&engine->proof_queue.lock);
    pthread_cond_destroy(&engine->proof_queue.not_empty);
    pthread_cond_destroy(&engine->proof_queue.not_full);
    
    free(engine);
}

/* Add vertex to current round */
bool streaming_dag_add_vertex(streaming_dag_engine_t* engine, dag_vertex_t* vertex) {
    pthread_mutex_lock(&engine->lock);
    
    /* Validate vertex round */
    if (vertex->round != engine->current_round) {
        pthread_mutex_unlock(&engine->lock);
        return false;
    }
    
    /* Allocate and copy vertex */
    dag_vertex_t* v = malloc(sizeof(dag_vertex_t));
    memcpy(v, vertex, sizeof(dag_vertex_t));
    v->hash = compute_vertex_hash(v);
    
    /* Add to round */
    dag_round_t* round = &engine->rounds[engine->current_round];
    round->vertices[round->vertex_count++] = v;
    engine->total_vertices++;
    
    /* Check if we should trigger proof generation */
    if (engine->streaming_enabled && round->vertex_count > 0) {
        uint32_t progress = (round->vertex_count * 100) / MAX_VALIDATORS;
        
        if (progress >= engine->proof_threshold && !round->round_hash.bytes[0]) {
            /* Mark round as being processed */
            round->round_hash.bytes[0] = 1;  /* Temporary marker */
            
            /* Queue for proof generation */
            pthread_mutex_lock(&engine->proof_queue.lock);
            
            /* Wait if queue full */
            uint32_t next_head = (engine->proof_queue.head + 1) % 16;
            while (next_head == engine->proof_queue.tail) {
                pthread_cond_wait(&engine->proof_queue.not_full, &engine->proof_queue.lock);
                next_head = (engine->proof_queue.head + 1) % 16;
            }
            
            engine->proof_queue.rounds[engine->proof_queue.head] = round;
            engine->proof_queue.head = next_head;
            pthread_cond_signal(&engine->proof_queue.not_empty);
            
            pthread_mutex_unlock(&engine->proof_queue.lock);
        }
    }
    
    pthread_mutex_unlock(&engine->lock);
    return true;
}

/* Complete current round and start next */
bool streaming_dag_complete_round(streaming_dag_engine_t* engine) {
    pthread_mutex_lock(&engine->lock);
    
    dag_round_t* round = &engine->rounds[engine->current_round];
    
    /* Validate round */
    if (!validate_round_structure(round)) {
        pthread_mutex_unlock(&engine->lock);
        return false;
    }
    
    /* Compute final round hash */
    round->round_hash = compute_round_merkle_root(round);
    round->timestamp = get_time_us();
    
    /* Notify callback */
    if (engine->on_round_complete) {
        engine->on_round_complete(
            engine->current_round,
            round,
            engine->callback_data
        );
    }
    
    /* If not streaming, generate proof now */
    if (!engine->streaming_enabled) {
        pthread_mutex_lock(&engine->proof_queue.lock);
        
        uint32_t next_head = (engine->proof_queue.head + 1) % 16;
        if (next_head != engine->proof_queue.tail) {
            engine->proof_queue.rounds[engine->proof_queue.head] = round;
            engine->proof_queue.head = next_head;
            pthread_cond_signal(&engine->proof_queue.not_empty);
        }
        
        pthread_mutex_unlock(&engine->proof_queue.lock);
    }
    
    /* Move to next round */
    engine->current_round++;
    
    pthread_mutex_unlock(&engine->lock);
    return true;
}

/* Get proof for specific round */
dag_round_proof_t* streaming_dag_get_proof(streaming_dag_engine_t* engine, uint32_t round) {
    if (round >= engine->current_round) return NULL;
    
    pthread_mutex_lock(&engine->lock);
    dag_round_proof_t* proof = &engine->round_proofs[round];
    pthread_mutex_unlock(&engine->lock);
    
    return proof->proof ? proof : NULL;
}

/* Verify streaming proof */
bool streaming_dag_verify_proof(dag_round_proof_t* proof, hash256_t genesis_hash) {
    if (!proof || !proof->proof) return false;
    
    /* Verify the circular recursive proof */
    blockchain_state_t genesis_state = {0};
    memcpy(genesis_state.state_hash, genesis_hash.bytes, 32);
    
    return basefold_raa_circular_verify(proof->proof, &genesis_state);
}

/* Light client update */
bool dag_light_client_update(dag_light_client_t* client, dag_round_proof_t* new_proof) {
    /* Verify new proof */
    if (!streaming_dag_verify_proof(new_proof, client->genesis_hash)) {
        return false;
    }
    
    /* Verify round progression */
    if (new_proof->round <= client->tracked_round) {
        return false;
    }
    
    /* Update state */
    client->tracked_round = new_proof->round;
    client->latest_proof = *new_proof;
    
    return true;
}

/* Get statistics */
streaming_dag_stats_t streaming_dag_get_stats(streaming_dag_engine_t* engine) {
    streaming_dag_stats_t stats = {0};
    
    pthread_mutex_lock(&engine->lock);
    
    if (engine->proofs_generated > 0) {
        stats.avg_proof_time_ms = (double)engine->total_proof_time_us / 
                                 engine->proofs_generated / 1000.0;
        stats.rounds_proven = engine->proofs_generated;
    }
    
    stats.total_vertices = engine->total_vertices;
    
    if (engine->total_proof_time_us > 0) {
        stats.throughput_vertices_per_sec = 
            (double)engine->total_vertices * 1000000.0 / engine->total_proof_time_us;
    }
    
    /* Calculate compression ratio */
    uint64_t original_size = engine->total_vertices * sizeof(dag_vertex_t);
    uint64_t proof_size = 190 * 1024;  /* ~190KB per proof */
    stats.compression_ratio = (double)original_size / proof_size;
    
    pthread_mutex_unlock(&engine->lock);
    
    return stats;
}