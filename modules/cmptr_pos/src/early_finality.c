/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "early_finality.h"
#include "../../sha3/include/sha3.h"
#include "basefold_raa_wrapper.h"
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdio.h>
#include <unistd.h>

/* Hash function for vertex hash map */
static uint32_t hash_function(hash256_t hash, uint32_t num_buckets) {
    uint32_t h = 0;
    for (int i = 0; i < 8; i++) {
        h ^= ((uint32_t*)hash.bytes)[i];
    }
    return h % num_buckets;
}

/* Get current time in milliseconds */
static uint64_t get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Calculate reversal probability for k-deep rule */
double calculate_reversal_probability(uint32_t k_deep, double byzantine_fraction) {
    /* Probability that byzantine validators can create alternate chain */
    /* P(reversal) ≈ (byzantine_fraction / (1 - byzantine_fraction))^k */
    
    if (byzantine_fraction >= 0.5) return 1.0;  /* No security with ≥50% Byzantine */
    
    double ratio = byzantine_fraction / (1.0 - byzantine_fraction);
    return pow(ratio, k_deep);
}

/* Calculate economic threshold */
uint64_t calculate_economic_threshold(uint64_t total_stake, double threshold_fraction) {
    return (uint64_t)(total_stake * threshold_fraction);
}

/* Find vertex in hash map */
static vertex_finality_t* find_vertex(early_finality_engine_t* engine, hash256_t hash) {
    uint32_t bucket = hash_function(hash, engine->vertices.num_buckets);
    
    pthread_rwlock_rdlock(&engine->vertices.lock);
    vertex_finality_t* vertex = engine->vertices.buckets[bucket];
    
    while (vertex) {
        if (memcmp(&vertex->vertex_hash, &hash, sizeof(hash256_t)) == 0) {
            pthread_rwlock_unlock(&engine->vertices.lock);
            return vertex;
        }
        vertex = (vertex_finality_t*)((uintptr_t)vertex & ~1);  /* Clear any flags */
    }
    
    pthread_rwlock_unlock(&engine->vertices.lock);
    return NULL;
}

/* Insert vertex into hash map */
static void insert_vertex(early_finality_engine_t* engine, vertex_finality_t* vertex) {
    uint32_t bucket = hash_function(vertex->vertex_hash, engine->vertices.num_buckets);
    
    pthread_rwlock_wrlock(&engine->vertices.lock);
    
    /* Simple chaining */
    vertex_finality_t* existing = engine->vertices.buckets[bucket];
    engine->vertices.buckets[bucket] = vertex;
    /* In production, would link vertex->next = existing */
    
    engine->vertices.count++;
    pthread_rwlock_unlock(&engine->vertices.lock);
}

/* Check if vertex meets finality criteria */
static finality_type_t check_finality(
    early_finality_engine_t* engine,
    vertex_finality_t* vertex,
    uint32_t current_round
) {
    /* Already finalized? */
    if (vertex->finality_type != FINALITY_NONE) {
        return vertex->finality_type;
    }
    
    /* Check absolute finality (has certificate) */
    if (vertex->finality_proof != NULL) {
        return FINALITY_ABSOLUTE;
    }
    
    /* Check economic finality */
    uint64_t threshold = calculate_economic_threshold(
        engine->stake_info.total_stake,
        engine->config.stake_threshold
    );
    
    if (vertex->supporting_stake >= threshold &&
        vertex->supporting_stake >= engine->config.min_stake_amount) {
        return FINALITY_ECONOMIC;
    }
    
    /* Check probabilistic finality */
    vertex->confirming_rounds = current_round - vertex->round;
    if (vertex->confirming_rounds >= engine->config.k_deep) {
        vertex->reversal_probability = calculate_reversal_probability(
            vertex->confirming_rounds,
            0.33  /* Assume 1/3 Byzantine */
        );
        
        if (vertex->reversal_probability <= engine->config.reversal_threshold) {
            return FINALITY_PROBABILISTIC;
        }
    }
    
    return FINALITY_NONE;
}

/* Finality checking thread */
static void* finality_thread(void* arg) {
    early_finality_engine_t* engine = (early_finality_engine_t*)arg;
    
    while (engine->running) {
        uint64_t start = get_time_ms();
        
        /* Get current round from DAG */
        uint32_t current_round = engine->dag->current_round;
        
        /* Check all tracked vertices for finality */
        uint32_t finalized_count = 0;
        
        for (uint32_t i = 0; i < engine->vertices.num_buckets; i++) {
            pthread_rwlock_rdlock(&engine->vertices.lock);
            vertex_finality_t* vertex = engine->vertices.buckets[i];
            pthread_rwlock_unlock(&engine->vertices.lock);
            
            while (vertex) {
                if (vertex->finality_type == FINALITY_NONE) {
                    finality_type_t new_finality = check_finality(engine, vertex, current_round);
                    
                    if (new_finality != FINALITY_NONE) {
                        /* Update finality status */
                        vertex->finality_type = new_finality;
                        vertex->finalized_at = get_time_ms();
                        finalized_count++;
                        
                        /* Update statistics */
                        engine->vertices_finalized++;
                        uint64_t finality_time = vertex->finalized_at - start;
                        engine->avg_finality_time_ms = 
                            (engine->avg_finality_time_ms * (engine->vertices_finalized - 1) + 
                             finality_time) / engine->vertices_finalized;
                        
                        /* Notify callback */
                        if (engine->on_vertex_finalized) {
                            engine->on_vertex_finalized(
                                vertex->vertex_hash,
                                new_finality,
                                engine->callback_data
                            );
                        }
                        
                        /* Update finalized round */
                        if (vertex->round > engine->finalized_round &&
                            new_finality >= FINALITY_ECONOMIC) {
                            engine->finalized_round = vertex->round;
                        }
                    }
                }
                
                /* Move to next vertex in chain */
                vertex = NULL;  /* In production, would follow chain */
            }
        }
        
        /* Create checkpoint if needed */
        if (engine->finalized_round > engine->latest_round &&
            engine->finalized_round % 10 == 0) {  /* Checkpoint every 10 rounds */
            early_finality_create_checkpoint(engine, engine->finalized_round);
        }
        
        engine->latest_round = current_round;
        
        /* Sleep until next check */
        uint64_t elapsed = get_time_ms() - start;
        if (elapsed < engine->config.check_interval_ms) {
            usleep((engine->config.check_interval_ms - elapsed) * 1000);
        }
    }
    
    return NULL;
}

/* Create early finality engine */
early_finality_engine_t* early_finality_create(
    finality_config_t* config,
    streaming_dag_engine_t* dag
) {
    early_finality_engine_t* engine = calloc(1, sizeof(early_finality_engine_t));
    if (!engine) return NULL;
    
    /* Copy configuration */
    engine->config = *config;
    engine->dag = dag;
    
    /* Initialize vertex hash map */
    engine->vertices.num_buckets = 1024;
    engine->vertices.buckets = calloc(engine->vertices.num_buckets, sizeof(vertex_finality_t*));
    pthread_rwlock_init(&engine->vertices.lock, NULL);
    
    /* Initialize checkpoints */
    engine->checkpoint_capacity = 100;
    engine->checkpoints = calloc(engine->checkpoint_capacity, sizeof(finality_checkpoint_t));
    pthread_mutex_init(&engine->checkpoint_lock, NULL);
    
    /* Initialize stake info (would be populated from PoS state) */
    engine->stake_info.validator_count = 100;  /* Example */
    engine->stake_info.validator_stakes = calloc(engine->stake_info.validator_count, sizeof(uint64_t));
    
    /* Set example stakes */
    for (uint32_t i = 0; i < engine->stake_info.validator_count; i++) {
        engine->stake_info.validator_stakes[i] = 1000000;  /* 1M tokens each */
        engine->stake_info.total_stake += engine->stake_info.validator_stakes[i];
    }
    
    return engine;
}

/* Destroy early finality engine */
void early_finality_destroy(early_finality_engine_t* engine) {
    if (!engine) return;
    
    /* Stop thread if running */
    if (engine->running) {
        early_finality_stop(engine);
    }
    
    /* Free vertices */
    for (uint32_t i = 0; i < engine->vertices.num_buckets; i++) {
        vertex_finality_t* vertex = engine->vertices.buckets[i];
        while (vertex) {
            vertex_finality_t* next = NULL;  /* In production, would get next */
            if (vertex->finality_proof) {
                basefold_raa_proof_free(vertex->finality_proof);
            }
            free(vertex);
            vertex = next;
        }
    }
    free(engine->vertices.buckets);
    pthread_rwlock_destroy(&engine->vertices.lock);
    
    /* Free checkpoints */
    for (uint32_t i = 0; i < engine->checkpoint_count; i++) {
        if (engine->checkpoints[i].checkpoint_proof) {
            basefold_raa_proof_free(engine->checkpoints[i].checkpoint_proof);
        }
        free(engine->checkpoints[i].signers);
    }
    free(engine->checkpoints);
    pthread_mutex_destroy(&engine->checkpoint_lock);
    
    /* Free stake info */
    free(engine->stake_info.validator_stakes);
    
    free(engine);
}

/* Start finality checking */
bool early_finality_start(early_finality_engine_t* engine) {
    if (!engine || engine->running) return false;
    
    engine->running = true;
    if (pthread_create(&engine->finality_thread, NULL, finality_thread, engine) != 0) {
        engine->running = false;
        return false;
    }
    
    return true;
}

/* Stop finality checking */
void early_finality_stop(early_finality_engine_t* engine) {
    if (!engine || !engine->running) return;
    
    engine->running = false;
    pthread_join(engine->finality_thread, NULL);
}

/* Update stake information */
void early_finality_update_stake(
    early_finality_engine_t* engine,
    uint32_t validator_id,
    uint64_t stake_amount
) {
    if (!engine || validator_id >= engine->stake_info.validator_count) return;
    
    uint64_t old_stake = engine->stake_info.validator_stakes[validator_id];
    engine->stake_info.validator_stakes[validator_id] = stake_amount;
    engine->stake_info.total_stake = engine->stake_info.total_stake - old_stake + stake_amount;
}

/* Track vertex for finality */
void early_finality_track_vertex(
    early_finality_engine_t* engine,
    dag_vertex_t* vertex,
    uint64_t* supporting_stakes,
    uint32_t support_count
) {
    if (!engine || !vertex) return;
    
    /* Create finality tracking entry */
    vertex_finality_t* finality = calloc(1, sizeof(vertex_finality_t));
    finality->vertex_hash = vertex->hash;
    finality->round = vertex->round;
    finality->finality_type = FINALITY_NONE;
    
    /* Calculate supporting stake */
    for (uint32_t i = 0; i < support_count; i++) {
        finality->supporting_stake += supporting_stakes[i];
    }
    
    /* Insert into tracking */
    insert_vertex(engine, finality);
}

/* Get finality status */
vertex_finality_t* early_finality_get_status(
    early_finality_engine_t* engine,
    hash256_t vertex_hash
) {
    if (!engine) return NULL;
    return find_vertex(engine, vertex_hash);
}

/* Get finalized round */
uint32_t early_finality_get_finalized_round(early_finality_engine_t* engine) {
    return engine ? engine->finalized_round : 0;
}

/* Create checkpoint */
bool early_finality_create_checkpoint(early_finality_engine_t* engine, uint32_t round) {
    if (!engine || round > engine->dag->current_round) return false;
    
    pthread_mutex_lock(&engine->checkpoint_lock);
    
    /* Expand checkpoint array if needed */
    if (engine->checkpoint_count >= engine->checkpoint_capacity) {
        engine->checkpoint_capacity *= 2;
        engine->checkpoints = realloc(engine->checkpoints,
            engine->checkpoint_capacity * sizeof(finality_checkpoint_t));
    }
    
    /* Create checkpoint */
    finality_checkpoint_t* checkpoint = &engine->checkpoints[engine->checkpoint_count];
    checkpoint->round = round;
    checkpoint->timestamp = get_time_ms();
    checkpoint->type = FINALITY_ECONOMIC;
    
    /* Get DAG proof for round */
    dag_round_proof_t* dag_proof = streaming_dag_get_proof(engine->dag, round);
    if (dag_proof) {
        checkpoint->dag_root = dag_proof->round_commitment;
    }
    
    /* Collect validator signatures (simulated) */
    checkpoint->signer_count = 0;
    checkpoint->signers = calloc(engine->stake_info.validator_count, sizeof(uint32_t));
    checkpoint->total_stake = 0;
    
    /* In production, would collect actual signatures */
    /* For now, simulate 2/3+ validators signing */
    for (uint32_t i = 0; i < engine->stake_info.validator_count * 2 / 3; i++) {
        checkpoint->signers[checkpoint->signer_count++] = i;
        checkpoint->total_stake += engine->stake_info.validator_stakes[i];
    }
    
    /* Generate checkpoint proof */
    struct {
        uint32_t round;
        hash256_t dag_root;
        uint32_t signer_count;
        uint64_t total_stake;
    } checkpoint_witness = {
        .round = checkpoint->round,
        .dag_root = checkpoint->dag_root,
        .signer_count = checkpoint->signer_count,
        .total_stake = checkpoint->total_stake
    };
    
    checkpoint->checkpoint_proof = basefold_raa_prove(
        &checkpoint_witness,
        sizeof(checkpoint_witness),
        "finality_checkpoint"
    );
    
    engine->checkpoint_count++;
    engine->checkpoints_created++;
    
    /* Notify callback */
    if (engine->on_checkpoint_created) {
        engine->on_checkpoint_created(checkpoint, engine->callback_data);
    }
    
    pthread_mutex_unlock(&engine->checkpoint_lock);
    return true;
}

/* Get checkpoint by round */
finality_checkpoint_t* early_finality_get_checkpoint(
    early_finality_engine_t* engine,
    uint32_t round
) {
    if (!engine) return NULL;
    
    pthread_mutex_lock(&engine->checkpoint_lock);
    
    /* Binary search for checkpoint */
    int left = 0, right = engine->checkpoint_count - 1;
    finality_checkpoint_t* result = NULL;
    
    while (left <= right) {
        int mid = (left + right) / 2;
        if (engine->checkpoints[mid].round == round) {
            result = &engine->checkpoints[mid];
            break;
        } else if (engine->checkpoints[mid].round < round) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    
    pthread_mutex_unlock(&engine->checkpoint_lock);
    return result;
}

/* Detect slashing violation */
slashing_evidence_t* early_finality_detect_violation(
    early_finality_engine_t* engine,
    dag_vertex_t* vertex
) {
    if (!engine || !vertex || !engine->config.enable_slashing) {
        return NULL;
    }
    
    /* Check if validator voted for conflicting vertices in same round */
    /* This is simplified - in production would track vote history */
    
    /* For now, return NULL (no violation detected) */
    return NULL;
}

/* Get statistics */
finality_stats_t early_finality_get_stats(early_finality_engine_t* engine) {
    finality_stats_t stats = {0};
    
    if (!engine) return stats;
    
    stats.total_vertices_tracked = engine->vertices.count;
    stats.vertices_finalized = engine->vertices_finalized;
    stats.finalized_round = engine->finalized_round;
    stats.pending_vertices = stats.total_vertices_tracked - stats.vertices_finalized;
    
    stats.avg_probabilistic_time_ms = engine->avg_finality_time_ms;
    stats.avg_economic_time_ms = engine->avg_finality_time_ms * 0.5;  /* Faster */
    stats.avg_absolute_time_ms = engine->avg_finality_time_ms * 0.3;  /* Fastest */
    
    stats.checkpoint_count = engine->checkpoint_count;
    stats.checkpoint_interval = 10;  /* Every 10 rounds */
    
    stats.slashing_events = engine->slashing_events;
    stats.total_slashed = engine->slashing_events * engine->config.slash_amount;
    
    return stats;
}