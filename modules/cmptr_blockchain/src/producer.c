/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>

/* SHA3 compatibility */
#ifdef HAS_SHA3
#include "sha3.h"
#else
static inline void sha3_256(const uint8_t* data, size_t len, uint8_t* hash) {
    for (int i = 0; i < 32; i++) {
        hash[i] = (uint8_t)(i ^ (len & 0xFF) ^ (data ? data[0] : 0));
    }
}
#endif

/* Producer block creation thread */
static void* producer_worker(void* arg) {
    node_t* node = (node_t*)arg;
    producer_t* prod = &node->data.producer;
    
    printf("Producer #%u worker started\n", prod->id);
    
    while (node->state == NODE_STATE_ACTIVE) {
        /* Wait for block interval */
        sleep(10);  /* 10 second blocks */
        
        pthread_mutex_lock(&prod->block_mutex);
        
        /* Create new block */
        block_t* new_block = calloc(1, sizeof(block_t));
        new_block->height = node->blockchain->height;
        new_block->timestamp = time(NULL) * 1000000;
        new_block->producer_id = prod->id;
        new_block->difficulty = node->consensus_config.pow_difficulty;
        
        /* Get previous block hash */
        if (node->blockchain->height > 0) {
            block_t* prev = cmptr_blockchain_get_block(
                node->blockchain, 
                node->blockchain->height - 1
            );
            if (prev) {
                sha3_256((uint8_t*)prev, sizeof(block_t), new_block->prev_hash);
            }
        }
        
        /* In real implementation:
         * 1. Collect recursive proofs from generators
         * 2. Create final block proof
         * 3. Mine PoW
         * 4. Broadcast block
         */
        
        printf("Producer #%u: Creating block #%lu\n", 
               prod->id, new_block->height);
        
        /* Add to blockchain */
        if (cmptr_blockchain_add_block(node->blockchain, new_block)) {
            prod->blocks_produced++;
            printf("Producer #%u: Block #%lu added to chain\n",
                   prod->id, new_block->height);
        }
        
        free(new_block);
        
        pthread_mutex_unlock(&prod->block_mutex);
    }
    
    return NULL;
}

/* Start producer */
bool producer_start(node_t* node) {
    if (!node || node->type != NODE_TYPE_PRODUCER) {
        return false;
    }
    
    pthread_t worker;
    if (pthread_create(&worker, NULL, producer_worker, node) != 0) {
        return false;
    }
    
    pthread_detach(worker);
    return true;
}

/* Mine block with PoW */
bool producer_mine_block(
    node_t* node,
    block_t* block,
    uint32_t difficulty
) {
    if (!node || !block) return false;
    
    uint64_t nonce = 0;
    uint8_t hash[32];
    
    while (true) {
        block->nonce = nonce;
        
        /* Hash block header */
        sha3_256((uint8_t*)block, sizeof(block_t), hash);
        
        /* Check difficulty */
        uint32_t zeros = 0;
        for (int i = 0; i < 32 && zeros < difficulty; i++) {
            if (hash[i] == 0) {
                zeros += 8;
            } else {
                uint8_t byte = hash[i];
                while ((byte & 0x80) == 0) {
                    zeros++;
                    byte <<= 1;
                }
                break;
            }
        }
        
        if (zeros >= difficulty) {
            return true;  /* Found solution */
        }
        
        nonce++;
        
        /* Check if we should stop */
        if (node->state != NODE_STATE_ACTIVE) {
            return false;
        }
    }
}