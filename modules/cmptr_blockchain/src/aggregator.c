/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Aggregator worker thread */
static void* aggregator_worker(void* arg) {
    node_t* node = (node_t*)arg;
    blockchain_aggregator_t* agg = &node->data.aggregator;
    
    printf("Aggregator #%u worker started\n", agg->id);
    
    while (node->state == NODE_STATE_ACTIVE) {
        pthread_mutex_lock(&agg->batch_mutex);
        
        if (agg->current_batch_size >= 1000) {
            /* Generate batch proof */
            printf("Aggregator #%u: Creating proof for %lu transactions\n",
                   agg->id, agg->current_batch_size);
            
            /* In real implementation:
             * 1. Create recursive proof of all transactions
             * 2. Send to generator node
             * 3. Clear batch
             */
            
            /* Clear batch */
            for (uint32_t i = 0; i < agg->current_batch_size; i++) {
                free(agg->pending_batch[i]);
            }
            agg->current_batch_size = 0;
        }
        
        pthread_mutex_unlock(&agg->batch_mutex);
        
        /* Rate limit to 1000 TPS */
        usleep(1000);  /* 1ms */
    }
    
    return NULL;
}

/* Start aggregator processing */
bool aggregator_start(node_t* node) {
    if (!node || node->type != NODE_TYPE_AGGREGATOR) {
        return false;
    }
    
    pthread_t worker;
    if (pthread_create(&worker, NULL, aggregator_worker, node) != 0) {
        return false;
    }
    
    pthread_detach(worker);
    return true;
}