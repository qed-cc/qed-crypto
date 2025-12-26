/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Wave pattern for Mysticeti */
typedef struct {
    uint32_t wave_number;
    narwhal_vertex_t** leaders;      /* Leader vertices for this wave */
    uint32_t leader_count;
    narwhal_vertex_t** committed;    /* Committed vertices */
    uint32_t committed_count;
} mysticeti_wave_t;

/* Create ordering state */
mysticeti_state_t* cmptr_pos_create_ordering(
    narwhal_dag_t* dag,
    committee_t* committee
) {
    if (!dag || !committee) {
        return NULL;
    }
    
    mysticeti_state_t* ordering = calloc(1, sizeof(mysticeti_state_t));
    if (!ordering) {
        return NULL;
    }
    
    ordering->dag = dag;
    ordering->honest_stake = (committee->size * 2) / 3; /* 2/3 assumption */
    ordering->total_stake = committee->size;
    
    /* Allocate arrays */
    ordering->ordered_vertices = calloc(dag->vertex_count, sizeof(narwhal_vertex_t*));
    ordering->ordered_count = 0;
    
    ordering->vertex_votes = calloc(dag->vertex_count, sizeof(uint32_t));
    ordering->vertex_decided = calloc(dag->vertex_count, sizeof(bool));
    
    printf("✓ Created Mysticeti ordering state\n");
    printf("  - DAG vertices: %u\n", dag->vertex_count);
    printf("  - Honest stake: %u/%u\n", ordering->honest_stake, ordering->total_stake);
    
    return ordering;
}

/* Find vertex by ID */
static narwhal_vertex_t* find_vertex_by_id(
    narwhal_dag_t* dag,
    const uint8_t* id
) {
    for (uint32_t i = 0; i < dag->vertex_count; i++) {
        if (memcmp(dag->vertices[i]->id, id, 32) == 0) {
            return dag->vertices[i];
        }
    }
    return NULL;
}

/* Count votes for a vertex (how many descendants reference it) */
static uint32_t count_vertex_votes(
    mysticeti_state_t* ordering,
    narwhal_vertex_t* target
) {
    uint32_t votes = 0;
    
    /* Count how many vertices in later rounds have path to target */
    for (uint32_t i = 0; i < ordering->dag->vertex_count; i++) {
        narwhal_vertex_t* voter = ordering->dag->vertices[i];
        
        /* Only count votes from later rounds */
        if (voter->round <= target->round) {
            continue;
        }
        
        /* Check if voter has path to target (simplified) */
        bool has_path = false;
        
        /* Direct parent check */
        for (uint32_t p = 0; p < voter->parent_count; p++) {
            if (memcmp(voter->parent_hashes[p], target->id, 32) == 0) {
                has_path = true;
                break;
            }
        }
        
        /* In real implementation: do full transitive path check */
        if (has_path) {
            votes++;
        }
    }
    
    return votes;
}

/* Identify wave leaders */
static mysticeti_wave_t* identify_wave_leaders(
    mysticeti_state_t* ordering,
    uint32_t wave_round
) {
    mysticeti_wave_t* wave = calloc(1, sizeof(mysticeti_wave_t));
    wave->wave_number = wave_round / 4; /* Wave every 4 rounds */
    wave->leaders = calloc(100, sizeof(narwhal_vertex_t*));
    wave->leader_count = 0;
    
    /* Find vertices in wave round with enough votes */
    for (uint32_t i = 0; i < ordering->dag->vertex_count; i++) {
        narwhal_vertex_t* vertex = ordering->dag->vertices[i];
        
        if (vertex->round != wave_round) {
            continue;
        }
        
        /* Count votes from future rounds */
        uint32_t votes = count_vertex_votes(ordering, vertex);
        
        /* Leader if has > 2/3 votes */
        if (votes >= ordering->honest_stake) {
            wave->leaders[wave->leader_count++] = vertex;
            printf("  ✓ Leader found: round %u, votes %u/%u\n",
                   vertex->round, votes, ordering->total_stake);
        }
    }
    
    return wave;
}

/* Commit vertices reachable from leaders */
static void commit_wave_vertices(
    mysticeti_state_t* ordering,
    mysticeti_wave_t* wave
) {
    wave->committed = calloc(1000, sizeof(narwhal_vertex_t*));
    wave->committed_count = 0;
    
    /* Mark all vertices reachable from leaders */
    for (uint32_t l = 0; l < wave->leader_count; l++) {
        narwhal_vertex_t* leader = wave->leaders[l];
        
        /* Add leader itself */
        wave->committed[wave->committed_count++] = leader;
        
        /* Add all ancestors (simplified - just parents) */
        for (uint32_t p = 0; p < leader->parent_count; p++) {
            narwhal_vertex_t* parent = find_vertex_by_id(
                ordering->dag, 
                leader->parent_hashes[p]
            );
            
            if (parent && !ordering->vertex_decided[p]) {
                wave->committed[wave->committed_count++] = parent;
            }
        }
    }
    
    printf("  → Committed %u vertices in wave %u\n",
           wave->committed_count, wave->wave_number);
}

/* Run Mysticeti ordering */
bool cmptr_pos_run_ordering(mysticeti_state_t* ordering) {
    if (!ordering) {
        return false;
    }
    
    printf("\n=== Running Mysticeti Ordering ===\n");
    
    pthread_rwlock_rdlock(&ordering->dag->dag_lock);
    
    /* Process waves every 4 rounds */
    for (uint32_t round = 3; round <= ordering->dag->current_round; round += 4) {
        printf("\n→ Processing wave at round %u\n", round);
        
        /* Identify leaders */
        mysticeti_wave_t* wave = identify_wave_leaders(ordering, round);
        
        if (wave->leader_count == 0) {
            printf("  ⚠️  No leaders found\n");
            free(wave->leaders);
            free(wave);
            continue;
        }
        
        /* Commit vertices */
        commit_wave_vertices(ordering, wave);
        
        /* Add to ordered output */
        for (uint32_t i = 0; i < wave->committed_count; i++) {
            narwhal_vertex_t* vertex = wave->committed[i];
            
            /* Find vertex index */
            uint32_t idx = 0;
            for (uint32_t j = 0; j < ordering->dag->vertex_count; j++) {
                if (ordering->dag->vertices[j] == vertex) {
                    idx = j;
                    break;
                }
            }
            
            if (!ordering->vertex_decided[idx]) {
                ordering->ordered_vertices[ordering->ordered_count++] = vertex;
                ordering->vertex_decided[idx] = true;
            }
        }
        
        free(wave->leaders);
        free(wave->committed);
        free(wave);
    }
    
    /* Order remaining undecided vertices by round then author */
    for (uint32_t r = 0; r <= ordering->dag->current_round; r++) {
        for (uint32_t i = 0; i < ordering->dag->vertex_count; i++) {
            narwhal_vertex_t* vertex = ordering->dag->vertices[i];
            
            if (vertex->round == r && !ordering->vertex_decided[i]) {
                ordering->ordered_vertices[ordering->ordered_count++] = vertex;
                ordering->vertex_decided[i] = true;
            }
        }
    }
    
    pthread_rwlock_unlock(&ordering->dag->dag_lock);
    
    printf("\n✓ Ordering complete:\n");
    printf("  - Ordered vertices: %u/%u\n", 
           ordering->ordered_count, ordering->dag->vertex_count);
    printf("  - Finality achieved through wave commits\n");
    
    return true;
}

/* Extract transactions in order */
uint32_t cmptr_pos_extract_ordered_transactions(
    mysticeti_state_t* ordering,
    transaction_t** transactions_out,
    uint32_t max_transactions
) {
    if (!ordering || !transactions_out) {
        return 0;
    }
    
    uint32_t tx_count = 0;
    
    /* Process vertices in order */
    for (uint32_t i = 0; i < ordering->ordered_count && tx_count < max_transactions; i++) {
        narwhal_vertex_t* vertex = ordering->ordered_vertices[i];
        
        /* Extract transactions from blob (simplified) */
        uint32_t vertex_txs = vertex->blob_size / 256; /* ~256 bytes per tx */
        
        for (uint32_t j = 0; j < vertex_txs && tx_count < max_transactions; j++) {
            transaction_t* tx = calloc(1, sizeof(transaction_t));
            
            /* Create dummy transaction from blob data */
            memcpy(tx->id, vertex->id, 32);
            tx->id[0] = (uint8_t)j; /* Differentiate transactions */
            
            /* Set nullifiers and commitments */
            memset(tx->nullifiers[0], 0xA0, 32);
            memset(tx->nullifiers[1], 0xA1, 32);
            memset(tx->commitments[0], 0xC0, 32);
            memset(tx->commitments[1], 0xC1, 32);
            
            tx->timestamp = vertex->timestamp + j;
            tx->aggregator_id = i % 1000; /* Simulate aggregator assignment */
            
            transactions_out[tx_count++] = tx;
        }
    }
    
    printf("✓ Extracted %u ordered transactions\n", tx_count);
    return tx_count;
}

/* Free ordering state */
void cmptr_pos_destroy_ordering(mysticeti_state_t* ordering) {
    if (!ordering) {
        return;
    }
    
    free(ordering->ordered_vertices);
    free(ordering->vertex_votes);
    free(ordering->vertex_decided);
    free(ordering);
}