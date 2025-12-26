/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>

/* Consensus thread function */
static void* consensus_thread_func(void* arg);

/* Initialize PoS system */
pos_state_t* cmptr_pos_init(
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain
) {
    if (!accumulator || !blockchain) {
        return NULL;
    }
    
    pos_state_t* pos = calloc(1, sizeof(pos_state_t));
    if (!pos) {
        return NULL;
    }
    
    /* Default configuration */
    pos->epoch_length = 32;           /* 32 blocks per epoch */
    pos->committee_size = 100;        /* 100 validators in committee */
    pos->min_stake = 32000000;        /* 32 tokens minimum */
    pos->unbonding_period = 256;      /* ~8 epochs to unbond */
    
    /* Initialize state */
    pos->current_epoch = 0;
    pos->current_slot = 0;
    pos->phase = PHASE_IDLE;
    
    /* Allocate validator storage */
    pos->validators = calloc(10000, sizeof(validator_pos_t*));
    pos->validator_count = 0;
    pos->total_staked = 0;
    
    /* Link to blockchain */
    pos->accumulator = accumulator;
    pos->blockchain = blockchain;
    
    /* Initialize mutex */
    pthread_mutex_init(&pos->state_mutex, NULL);
    pos->is_running = false;
    
    printf("✓ PoS system initialized\n");
    printf("  - Epoch length: %u blocks\n", pos->epoch_length);
    printf("  - Committee size: %u validators\n", pos->committee_size);
    printf("  - Min stake: %lu tokens\n", pos->min_stake);
    
    return pos;
}

/* Destroy PoS system */
void cmptr_pos_destroy(pos_state_t* pos) {
    if (!pos) return;
    
    /* Stop consensus if running */
    if (pos->is_running) {
        cmptr_pos_stop_consensus(pos);
    }
    
    /* Free validators */
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        free(pos->validators[i]);
    }
    free(pos->validators);
    
    /* Free consensus state */
    if (pos->current_committee) {
        free(pos->current_committee->members);
        free(pos->current_committee);
    }
    
    if (pos->current_dag) {
        /* Free DAG vertices */
        for (uint32_t i = 0; i < pos->current_dag->vertex_count; i++) {
            free(pos->current_dag->vertices[i]->blob_data);
            free(pos->current_dag->vertices[i]);
        }
        free(pos->current_dag->vertices);
        free(pos->current_dag->round_sizes);
        pthread_rwlock_destroy(&pos->current_dag->dag_lock);
        free(pos->current_dag);
    }
    
    if (pos->ordering_state) {
        free(pos->ordering_state->ordered_vertices);
        free(pos->ordering_state->vertex_votes);
        free(pos->ordering_state->vertex_decided);
        free(pos->ordering_state);
    }
    
    pthread_mutex_destroy(&pos->state_mutex);
    free(pos);
}

/* Add validator */
bool cmptr_pos_add_validator(
    pos_state_t* pos,
    const uint8_t* public_key,
    uint64_t stake_amount,
    const uint8_t* vrf_public_key
) {
    if (!pos || !public_key || !vrf_public_key) {
        return false;
    }
    
    /* Check minimum stake */
    if (stake_amount < pos->min_stake) {
        fprintf(stderr, "Stake amount below minimum: %lu < %lu\n",
                stake_amount, pos->min_stake);
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Check if validator already exists */
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (memcmp(pos->validators[i]->public_key, public_key, 32) == 0) {
            pthread_mutex_unlock(&pos->state_mutex);
            fprintf(stderr, "Validator already exists\n");
            return false;
        }
    }
    
    /* Create new validator */
    validator_pos_t* validator = calloc(1, sizeof(validator_pos_t));
    memcpy(validator->public_key, public_key, 32);
    validator->stake_amount = stake_amount;
    validator->state = STAKE_STATE_PENDING;
    validator->activation_epoch = pos->current_epoch + 2; /* Active in 2 epochs */
    validator->exit_epoch = UINT64_MAX;
    
    /* Copy VRF key */
    memcpy(validator->vrf_public_key, vrf_public_key, 64);
    
    /* Add to validator set */
    pos->validators[pos->validator_count++] = validator;
    pos->total_staked += stake_amount;
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Added validator with stake: %lu\n", stake_amount);
    return true;
}

/* Start consensus */
bool cmptr_pos_start_consensus(pos_state_t* pos) {
    if (!pos || pos->is_running) {
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Check minimum validators */
    uint32_t active_count = 0;
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (pos->validators[i]->state == STAKE_STATE_ACTIVE) {
            active_count++;
        }
    }
    
    if (active_count < pos->committee_size) {
        pthread_mutex_unlock(&pos->state_mutex);
        fprintf(stderr, "Not enough active validators: %u < %u\n",
                active_count, pos->committee_size);
        return false;
    }
    
    /* Start consensus thread */
    pos->is_running = true;
    if (pthread_create(&pos->consensus_thread, NULL, 
                      consensus_thread_func, pos) != 0) {
        pos->is_running = false;
        pthread_mutex_unlock(&pos->state_mutex);
        return false;
    }
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Consensus started with %u active validators\n", active_count);
    return true;
}

/* Stop consensus */
bool cmptr_pos_stop_consensus(pos_state_t* pos) {
    if (!pos || !pos->is_running) {
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    pos->is_running = false;
    pthread_mutex_unlock(&pos->state_mutex);
    
    /* Wait for consensus thread */
    pthread_join(pos->consensus_thread, NULL);
    
    printf("✓ Consensus stopped\n");
    return true;
}

/* Consensus thread */
static void* consensus_thread_func(void* arg) {
    pos_state_t* pos = (pos_state_t*)arg;
    
    while (pos->is_running) {
        pthread_mutex_lock(&pos->state_mutex);
        
        /* Check if we need to advance epoch */
        if (pos->current_slot % pos->epoch_length == 0 && 
            pos->current_slot > 0) {
            pos->current_epoch++;
            printf("\n=== Epoch %u ===\n", pos->current_epoch);
            
            /* Update validator states */
            for (uint32_t i = 0; i < pos->validator_count; i++) {
                validator_pos_t* val = pos->validators[i];
                
                /* Activate pending validators */
                if (val->state == STAKE_STATE_PENDING &&
                    val->activation_epoch <= pos->current_epoch) {
                    val->state = STAKE_STATE_ACTIVE;
                    printf("✓ Validator activated\n");
                }
                
                /* Process exits */
                if (val->state == STAKE_STATE_UNBONDING &&
                    val->exit_epoch <= pos->current_epoch) {
                    val->state = STAKE_STATE_INACTIVE;
                    pos->total_staked -= val->stake_amount;
                    printf("✓ Validator exited\n");
                }
            }
        }
        
        /* Run consensus phases */
        switch (pos->phase) {
            case PHASE_IDLE:
                pos->phase = PHASE_STAKE_SNAPSHOT;
                break;
                
            case PHASE_STAKE_SNAPSHOT:
                printf("→ Taking stake snapshot...\n");
                /* In full implementation: create Verkle commitment */
                pos->phase = PHASE_VRF_ELECTION;
                break;
                
            case PHASE_VRF_ELECTION:
                printf("→ Running VRF election...\n");
                /* In full implementation: select committee via VRF */
                pos->phase = PHASE_DAG_CONSTRUCTION;
                break;
                
            case PHASE_DAG_CONSTRUCTION:
                printf("→ Building Narwhal DAG...\n");
                /* In full implementation: validators submit vertices */
                pos->phase = PHASE_ORDERING;
                break;
                
            case PHASE_ORDERING:
                printf("→ Running Mysticeti ordering...\n");
                /* In full implementation: order DAG vertices */
                pos->phase = PHASE_STARK_GENERATION;
                break;
                
            case PHASE_STARK_GENERATION:
                printf("→ Generating STARK certificate...\n");
                /* In full implementation: create recursive proof */
                pos->phase = PHASE_FINALIZATION;
                break;
                
            case PHASE_FINALIZATION:
                printf("✓ Block finalized at slot %lu\n", pos->current_slot);
                pos->current_slot++;
                pos->phase = PHASE_IDLE;
                break;
        }
        
        pthread_mutex_unlock(&pos->state_mutex);
        
        /* Simulate consensus timing */
        usleep(100000); /* 100ms per phase */
    }
    
    return NULL;
}

/* Get metrics */
pos_metrics_t cmptr_pos_get_metrics(const pos_state_t* pos) {
    pos_metrics_t metrics = {0};
    
    if (!pos) {
        return metrics;
    }
    
    pthread_mutex_lock((pthread_mutex_t*)&pos->state_mutex);
    
    metrics.current_epoch = pos->current_epoch;
    metrics.current_slot = pos->current_slot;
    metrics.validator_count = pos->validator_count;
    metrics.total_staked = pos->total_staked;
    metrics.committee_size = pos->committee_size;
    
    /* Count active validators */
    uint32_t active = 0;
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (pos->validators[i]->state == STAKE_STATE_ACTIVE) {
            active++;
        }
    }
    
    metrics.finality_time_ms = 600.0; /* 6 phases * 100ms */
    
    pthread_mutex_unlock((pthread_mutex_t*)&pos->state_mutex);
    
    return metrics;
}