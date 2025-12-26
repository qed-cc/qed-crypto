/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos_v2.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <pthread.h>
#include <unistd.h>

/* Streaming DAG state */
typedef struct {
    narwhal_dag_t* dag;
    uint32_t causality_threshold;     /* How many vertices trigger ordering */
    uint32_t vertices_since_ordering; /* Counter */
    bool ordering_in_progress;
    pthread_mutex_t stream_mutex;
    pthread_cond_t ordering_ready;
    
    /* Causal closure tracking */
    uint32_t* vertex_ancestors;       /* Count of ancestors per vertex */
    bool* vertex_has_closure;         /* Whether vertex has causal closure */
} streaming_dag_state_t;

/* Global streaming state (would be part of pos_state_v2_t) */
static streaming_dag_state_t* g_streaming_state = NULL;

/* Enable streaming DAG mode */
bool cmptr_pos_enable_streaming_dag(
    pos_state_v2_t* pos,
    uint32_t causality_threshold
) {
    if (!pos || !pos->streaming_dag_enabled) {
        return false;
    }
    
    /* Create streaming state */
    streaming_dag_state_t* state = calloc(1, sizeof(streaming_dag_state_t));
    if (!state) {
        return false;
    }
    
    /* Initialize DAG if not exists */
    if (!pos->base.current_dag) {
        pos->base.current_dag = cmptr_pos_create_dag();
        if (!pos->base.current_dag) {
            free(state);
            return false;
        }
    }
    
    state->dag = pos->base.current_dag;
    state->causality_threshold = causality_threshold;
    state->vertices_since_ordering = 0;
    state->ordering_in_progress = false;
    
    /* Allocate tracking arrays */
    state->vertex_ancestors = calloc(10000, sizeof(uint32_t));
    state->vertex_has_closure = calloc(10000, sizeof(bool));
    
    pthread_mutex_init(&state->stream_mutex, NULL);
    pthread_cond_init(&state->ordering_ready, NULL);
    
    /* Store globally for demo (would be in pos_state_v2_t) */
    g_streaming_state = state;
    
    /* Switch to streaming mode */
    pos->current_mode = CONSENSUS_MODE_STREAMING;
    
    printf("✓ Enabled streaming DAG mode\n");
    printf("  - Causality threshold: %u vertices\n", causality_threshold);
    printf("  - Continuous vertex processing\n");
    printf("  - Adaptive ordering triggers\n");
    
    return true;
}

/* Check if vertex has causal closure */
static bool check_causal_closure(
    streaming_dag_state_t* state,
    narwhal_vertex_t* vertex,
    uint32_t vertex_idx
) {
    if (!state || !vertex) {
        return false;
    }
    
    /* Count ancestors (simplified - just parents for demo) */
    uint32_t ancestor_count = 0;
    
    for (uint32_t p = 0; p < vertex->parent_count; p++) {
        /* Find parent vertex */
        for (uint32_t i = 0; i < state->dag->vertex_count; i++) {
            if (memcmp(state->dag->vertices[i]->id, 
                      vertex->parent_hashes[p], 32) == 0) {
                /* Add parent's ancestors + 1 */
                ancestor_count += state->vertex_ancestors[i] + 1;
                break;
            }
        }
    }
    
    state->vertex_ancestors[vertex_idx] = ancestor_count;
    
    /* Check if we have enough causal history */
    if (ancestor_count >= state->causality_threshold) {
        state->vertex_has_closure[vertex_idx] = true;
        return true;
    }
    
    return false;
}

/* Process vertex in streaming mode */
bool cmptr_pos_process_streaming_vertex(
    pos_state_v2_t* pos,
    const narwhal_vertex_t* vertex
) {
    if (!pos || !vertex || !g_streaming_state) {
        return false;
    }
    
    streaming_dag_state_t* state = g_streaming_state;
    
    pthread_mutex_lock(&state->stream_mutex);
    
    /* Add vertex to DAG */
    if (!cmptr_pos_add_vertex(state->dag, vertex)) {
        pthread_mutex_unlock(&state->stream_mutex);
        return false;
    }
    
    uint32_t vertex_idx = state->dag->vertex_count - 1;
    
    printf("→ Streaming: Added vertex from round %u (total: %u)\n",
           vertex->round, state->dag->vertex_count);
    
    /* Check causal closure */
    bool has_closure = check_causal_closure(state, 
                                           state->dag->vertices[vertex_idx],
                                           vertex_idx);
    
    if (has_closure) {
        printf("  ✓ Vertex has causal closure (%u ancestors)\n",
               state->vertex_ancestors[vertex_idx]);
    }
    
    /* Increment counter */
    state->vertices_since_ordering++;
    
    /* Trigger ordering if:
     * 1. We have enough vertices with causal closure
     * 2. Not already ordering
     * 3. Threshold reached
     */
    uint32_t closure_count = 0;
    for (uint32_t i = 0; i < state->dag->vertex_count; i++) {
        if (state->vertex_has_closure[i]) {
            closure_count++;
        }
    }
    
    bool should_order = (closure_count >= state->causality_threshold) &&
                       (!state->ordering_in_progress) &&
                       (state->vertices_since_ordering >= state->causality_threshold);
    
    if (should_order) {
        printf("\n=== Streaming ordering triggered ===\n");
        printf("  - Vertices with closure: %u\n", closure_count);
        printf("  - Vertices since last ordering: %u\n", 
               state->vertices_since_ordering);
        
        state->ordering_in_progress = true;
        state->vertices_since_ordering = 0;
        
        /* Signal ordering thread */
        pthread_cond_signal(&state->ordering_ready);
    }
    
    pthread_mutex_unlock(&state->stream_mutex);
    
    return true;
}

/* Streaming consensus worker (would run in separate thread) */
static void* streaming_consensus_worker(void* arg) {
    pos_state_v2_t* pos = (pos_state_v2_t*)arg;
    streaming_dag_state_t* state = g_streaming_state;
    
    if (!pos || !state) {
        return NULL;
    }
    
    while (pos->base.is_running) {
        pthread_mutex_lock(&state->stream_mutex);
        
        /* Wait for ordering signal */
        while (!state->ordering_in_progress && pos->base.is_running) {
            pthread_cond_wait(&state->ordering_ready, &state->stream_mutex);
        }
        
        if (!pos->base.is_running) {
            pthread_mutex_unlock(&state->stream_mutex);
            break;
        }
        
        printf("\n→ Streaming consensus: Running Mysticeti ordering...\n");
        
        /* Create ordering state */
        committee_t* committee = pos->base.current_committee;
        if (!committee) {
            /* Create dummy committee for demo */
            committee = calloc(1, sizeof(committee_t));
            committee->size = 100;
            committee->threshold = 67;
        }
        
        mysticeti_state_t* ordering = cmptr_pos_create_ordering(
            state->dag, committee
        );
        
        pthread_mutex_unlock(&state->stream_mutex);
        
        if (ordering) {
            /* Run ordering (this could take some time) */
            cmptr_pos_run_ordering(ordering);
            
            /* Extract ordered transactions */
            transaction_t** ordered_txs = calloc(100000, sizeof(transaction_t*));
            uint32_t tx_count = cmptr_pos_extract_ordered_transactions(
                ordering, ordered_txs, 100000
            );
            
            printf("✓ Ordered %u transactions\n", tx_count);
            
            /* In real implementation: produce block with transactions */
            
            /* Clean up */
            for (uint32_t i = 0; i < tx_count; i++) {
                free(ordered_txs[i]);
            }
            free(ordered_txs);
            cmptr_pos_destroy_ordering(ordering);
        }
        
        if (committee != pos->base.current_committee) {
            free(committee);
        }
        
        pthread_mutex_lock(&state->stream_mutex);
        state->ordering_in_progress = false;
        pthread_mutex_unlock(&state->stream_mutex);
        
        /* Brief pause before next ordering */
        usleep(100000);  /* 100ms */
    }
    
    return NULL;
}

/* Demonstrate streaming DAG benefits */
void cmptr_pos_streaming_dag_demo(pos_state_v2_t* pos) {
    if (!pos || !g_streaming_state) {
        return;
    }
    
    printf("\n=== Streaming DAG Demo ===\n");
    printf("Traditional approach: Wait for fixed rounds\n");
    printf("Streaming approach: Process continuously\n\n");
    
    /* Simulate vertex arrivals at different rates */
    for (int i = 0; i < 20; i++) {
        /* Create dummy vertex */
        narwhal_vertex_t* vertex = calloc(1, sizeof(narwhal_vertex_t));
        
        /* Random arrival time (simulating network delays) */
        int delay_ms = rand() % 50;  /* 0-50ms */
        
        /* Set vertex data */
        vertex->round = g_streaming_state->dag->current_round;
        memset(vertex->id, i, 32);
        memset(vertex->author, i % 10, 32);
        vertex->timestamp = time(NULL) * 1000000 + (delay_ms * 1000);
        
        /* Add parents from previous vertices */
        vertex->parent_count = 0;
        if (i > 0) {
            int num_parents = (rand() % 3) + 1;  /* 1-3 parents */
            for (int p = 0; p < num_parents && p < i; p++) {
                int parent_idx = i - p - 1;
                memcpy(vertex->parent_hashes[vertex->parent_count],
                       g_streaming_state->dag->vertices[parent_idx]->id, 32);
                vertex->parent_count++;
            }
        }
        
        /* Simulate blob data */
        vertex->blob_size = 10240;  /* 10KB */
        vertex->blob_data = calloc(vertex->blob_size, 1);
        
        printf("Time %dms: Vertex arrives from validator %d\n",
               i * 50 + delay_ms, i % 10);
        
        /* Process in streaming mode */
        cmptr_pos_process_streaming_vertex(pos, vertex);
        
        /* Clean up */
        free(vertex->blob_data);
        free(vertex);
        
        /* Simulate network delays */
        usleep(delay_ms * 1000);
    }
    
    printf("\n✓ Streaming benefits:\n");
    printf("  - No fixed round delays\n");
    printf("  - Adaptive ordering based on causal closure\n");
    printf("  - Better latency for well-connected validators\n");
    printf("  - Resilient to network partitions\n");
}

/* Clean up streaming state */
void cmptr_pos_disable_streaming_dag(pos_state_v2_t* pos) {
    if (!pos || !g_streaming_state) {
        return;
    }
    
    streaming_dag_state_t* state = g_streaming_state;
    
    /* Clean up */
    pthread_mutex_destroy(&state->stream_mutex);
    pthread_cond_destroy(&state->ordering_ready);
    free(state->vertex_ancestors);
    free(state->vertex_has_closure);
    free(state);
    
    g_streaming_state = NULL;
    
    /* Switch back to normal mode */
    pos->current_mode = CONSENSUS_MODE_NORMAL;
    
    printf("✓ Disabled streaming DAG mode\n");
}