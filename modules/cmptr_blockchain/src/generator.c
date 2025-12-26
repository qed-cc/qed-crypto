/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>
#include <unistd.h>

/* Generator worker thread */
static void* generator_worker(void* arg) {
    node_t* node = (node_t*)arg;
    generator_t* gen = &node->data.generator;
    
    printf("Generator #%u worker started\n", gen->id);
    
    while (node->state == NODE_STATE_ACTIVE) {
        if (gen->is_generating) {
            /* In real implementation:
             * 1. Collect proofs from 10 aggregators
             * 2. Create recursive proof combining them
             * 3. Send to producer node
             */
            
            printf("Generator #%u: Creating recursive proof from aggregators\n", 
                   gen->id);
            
            gen->proofs_generated++;
            gen->is_generating = false;
            
            /* Simulate proof generation time (~150ms) */
            usleep(150000);
        }
        
        usleep(10000);  /* 10ms */
    }
    
    return NULL;
}

/* Start generator processing */
bool generator_start(node_t* node) {
    if (!node || node->type != NODE_TYPE_GENERATOR) {
        return false;
    }
    
    generator_t* gen = &node->data.generator;
    
    /* Start worker threads */
    for (int i = 0; i < 4; i++) {
        if (pthread_create(&gen->worker_threads[i], NULL, 
                          generator_worker, node) != 0) {
            return false;
        }
        pthread_detach(gen->worker_threads[i]);
    }
    
    return true;
}

/* Request proof generation */
void generator_request_proof(node_t* node) {
    if (!node || node->type != NODE_TYPE_GENERATOR) return;
    
    generator_t* gen = &node->data.generator;
    gen->is_generating = true;
}