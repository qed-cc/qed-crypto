/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>

/* Hash function for vertex IDs */
static void compute_vertex_hash(
    uint8_t* hash_out,
    uint32_t round,
    const uint8_t* author,
    const uint8_t* blob_hash,
    const uint8_t parent_hashes[][32],
    uint32_t parent_count
) {
    /* In real: use SHA3-256 */
    memset(hash_out, 0, 32);
    memcpy(hash_out, &round, 4);
    memcpy(hash_out + 4, author, 8);
    memcpy(hash_out + 12, blob_hash, 8);
    if (parent_count > 0) {
        memcpy(hash_out + 20, parent_hashes[0], 8);
    }
    hash_out[0] ^= 0xDA; /* DAG marker */
}

/* Create DAG */
narwhal_dag_t* cmptr_pos_create_dag(void) {
    narwhal_dag_t* dag = calloc(1, sizeof(narwhal_dag_t));
    if (!dag) {
        return NULL;
    }
    
    /* Initialize storage */
    dag->vertices = calloc(10000, sizeof(narwhal_vertex_t*));
    dag->vertex_count = 0;
    dag->current_round = 0;
    
    dag->max_rounds = 100;
    dag->round_sizes = calloc(dag->max_rounds, sizeof(uint32_t));
    
    /* Initialize lock */
    pthread_rwlock_init(&dag->dag_lock, NULL);
    
    printf("✓ Created Narwhal DAG\n");
    return dag;
}

/* Add vertex to DAG */
bool cmptr_pos_add_vertex(
    narwhal_dag_t* dag,
    const narwhal_vertex_t* vertex
) {
    if (!dag || !vertex) {
        return false;
    }
    
    pthread_rwlock_wrlock(&dag->dag_lock);
    
    /* Validate vertex */
    if (vertex->round > dag->current_round + 1) {
        pthread_rwlock_unlock(&dag->dag_lock);
        fprintf(stderr, "Vertex round too far ahead: %u > %u\n",
                vertex->round, dag->current_round + 1);
        return false;
    }
    
    /* Verify parents exist (except for round 0) */
    if (vertex->round > 0 && vertex->parent_count == 0) {
        pthread_rwlock_unlock(&dag->dag_lock);
        fprintf(stderr, "Non-genesis vertex has no parents\n");
        return false;
    }
    
    /* Create copy of vertex */
    narwhal_vertex_t* new_vertex = calloc(1, sizeof(narwhal_vertex_t));
    memcpy(new_vertex, vertex, sizeof(narwhal_vertex_t));
    
    /* Deep copy blob data */
    if (vertex->blob_size > 0 && vertex->blob_data) {
        new_vertex->blob_data = malloc(vertex->blob_size);
        memcpy(new_vertex->blob_data, vertex->blob_data, vertex->blob_size);
    }
    
    /* Add to DAG */
    dag->vertices[dag->vertex_count++] = new_vertex;
    dag->round_sizes[vertex->round]++;
    
    /* Update current round */
    if (vertex->round > dag->current_round) {
        dag->current_round = vertex->round;
        printf("→ Advanced DAG to round %u\n", dag->current_round);
    }
    
    pthread_rwlock_unlock(&dag->dag_lock);
    
    return true;
}

/* Create a vertex for a validator */
narwhal_vertex_t* cmptr_pos_create_vertex(
    narwhal_dag_t* dag,
    const validator_pos_t* validator,
    const uint8_t* blob_data,
    uint32_t blob_size
) {
    if (!dag || !validator || !blob_data || blob_size == 0) {
        return NULL;
    }
    
    narwhal_vertex_t* vertex = calloc(1, sizeof(narwhal_vertex_t));
    if (!vertex) {
        return NULL;
    }
    
    pthread_rwlock_rdlock(&dag->dag_lock);
    
    /* Set round */
    vertex->round = dag->current_round;
    
    /* Set author */
    memcpy(vertex->author, validator->public_key, 32);
    
    /* Find parents from previous round */
    vertex->parent_count = 0;
    if (vertex->round > 0) {
        /* Include up to 4 parents from previous round */
        for (uint32_t i = 0; i < dag->vertex_count && vertex->parent_count < 4; i++) {
            narwhal_vertex_t* candidate = dag->vertices[i];
            if (candidate->round == vertex->round - 1) {
                memcpy(vertex->parent_hashes[vertex->parent_count], 
                       candidate->id, 32);
                vertex->parent_count++;
            }
        }
    }
    
    pthread_rwlock_unlock(&dag->dag_lock);
    
    /* Set blob data */
    vertex->blob_data = malloc(blob_size);
    memcpy(vertex->blob_data, blob_data, blob_size);
    vertex->blob_size = blob_size;
    
    /* Compute blob hash */
    /* In real: use SHA3-256 */
    memset(vertex->blob_hash, 0, 32);
    for (uint32_t i = 0; i < blob_size && i < 32; i++) {
        vertex->blob_hash[i] = blob_data[i];
    }
    vertex->blob_hash[0] ^= 0xBB; /* Blob marker */
    
    /* Compute vertex ID */
    compute_vertex_hash(
        vertex->id,
        vertex->round,
        vertex->author,
        vertex->blob_hash,
        vertex->parent_hashes,
        vertex->parent_count
    );
    
    /* Set timestamp */
    vertex->timestamp = time(NULL) * 1000000; /* Microseconds */
    
    /* Sign vertex (simplified) */
    memset(vertex->signature, 0xAA, 64);
    memcpy(vertex->signature, vertex->id, 32);
    memcpy(vertex->signature + 32, validator->public_key, 32);
    
    printf("✓ Created vertex:\n");
    printf("  - Round: %u\n", vertex->round);
    printf("  - Parents: %u\n", vertex->parent_count);
    printf("  - Blob size: %u bytes\n", vertex->blob_size);
    printf("  - ID: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", vertex->id[i]);
    }
    printf("...\n");
    
    return vertex;
}

/* Simulate DAG construction for a round */
bool cmptr_pos_simulate_dag_round(
    narwhal_dag_t* dag,
    committee_t* committee,
    uint32_t transactions_per_validator
) {
    if (!dag || !committee) {
        return false;
    }
    
    printf("\n→ Simulating DAG round %u\n", dag->current_round + 1);
    
    /* Each committee member creates a vertex */
    for (uint32_t i = 0; i < committee->size; i++) {
        validator_pos_t* validator = committee->members[i];
        
        /* Create blob with transactions */
        uint32_t blob_size = transactions_per_validator * 256; /* ~256 bytes per tx */
        uint8_t* blob = malloc(blob_size);
        
        /* Fill with dummy transaction data */
        for (uint32_t j = 0; j < blob_size; j++) {
            blob[j] = (uint8_t)((i + j) & 0xFF);
        }
        
        /* Create vertex */
        narwhal_vertex_t* vertex = cmptr_pos_create_vertex(
            dag, validator, blob, blob_size
        );
        
        if (vertex) {
            /* Add to DAG */
            cmptr_pos_add_vertex(dag, vertex);
            free(vertex->blob_data);
            free(vertex);
        }
        
        free(blob);
    }
    
    printf("✓ Round %u complete: %u vertices added\n",
           dag->current_round, committee->size);
    
    return true;
}

/* Get DAG statistics */
void cmptr_pos_dag_stats(const narwhal_dag_t* dag) {
    if (!dag) {
        return;
    }
    
    pthread_rwlock_rdlock((pthread_rwlock_t*)&dag->dag_lock);
    
    uint64_t total_blob_size = 0;
    uint32_t max_round_size = 0;
    
    for (uint32_t i = 0; i < dag->vertex_count; i++) {
        total_blob_size += dag->vertices[i]->blob_size;
    }
    
    for (uint32_t r = 0; r <= dag->current_round; r++) {
        if (dag->round_sizes[r] > max_round_size) {
            max_round_size = dag->round_sizes[r];
        }
    }
    
    pthread_rwlock_unlock((pthread_rwlock_t*)&dag->dag_lock);
    
    printf("\nDAG Statistics:\n");
    printf("  - Current round: %u\n", dag->current_round);
    printf("  - Total vertices: %u\n", dag->vertex_count);
    printf("  - Total data: %.2f MB\n", total_blob_size / (1024.0 * 1024.0));
    printf("  - Max round size: %u vertices\n", max_round_size);
    printf("  - Avg blob size: %.2f KB\n", 
           dag->vertex_count > 0 ? 
           (total_blob_size / dag->vertex_count) / 1024.0 : 0);
}

/* Free DAG */
void cmptr_pos_destroy_dag(narwhal_dag_t* dag) {
    if (!dag) {
        return;
    }
    
    /* Free all vertices */
    for (uint32_t i = 0; i < dag->vertex_count; i++) {
        if (dag->vertices[i]) {
            free(dag->vertices[i]->blob_data);
            free(dag->vertices[i]);
        }
    }
    
    free(dag->vertices);
    free(dag->round_sizes);
    pthread_rwlock_destroy(&dag->dag_lock);
    free(dag);
}