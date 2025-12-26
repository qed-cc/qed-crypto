/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include "consensus.h"
#include "networking.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>

/* SHA3 compatibility */
#ifdef HAS_SHA3
#include "sha3.h"
#else
static inline void sha3_256(const uint8_t* data, size_t len, uint8_t* hash) {
    /* Stub for testing */
    for (int i = 0; i < 32; i++) {
        hash[i] = (uint8_t)(i ^ (len & 0xFF) ^ (data ? data[0] : 0));
    }
}
#endif

/* Initialize blockchain */
blockchain_t* cmptr_blockchain_init(void) {
    blockchain_t* blockchain = calloc(1, sizeof(blockchain_t));
    if (!blockchain) return NULL;
    
    /* Initialize chain storage */
    blockchain->blocks = calloc(10000, sizeof(block_t*));  /* Initial capacity */
    blockchain->height = 0;
    blockchain->total_transactions = 0;
    
    /* Initialize synchronization */
    pthread_rwlock_init(&blockchain->chain_lock, NULL);
    blockchain->is_syncing = false;
    blockchain->sync_target_height = 0;
    
    /* Create genesis block */
    block_t* genesis = calloc(1, sizeof(block_t));
    genesis->height = 0;
    memset(genesis->prev_hash, 0, 32);
    genesis->timestamp = time(NULL) * 1000000;  /* Microseconds */
    genesis->difficulty = 20;  /* Initial difficulty */
    
    /* Genesis message */
    const char* genesis_msg = "CMPTR Blockchain Genesis - Solving the Trilemma";
    sha3_256((uint8_t*)genesis_msg, strlen(genesis_msg), genesis->merkle_root);
    
    blockchain->blocks[0] = genesis;
    blockchain->height = 1;
    
    return blockchain;
}

/* Destroy blockchain */
void cmptr_blockchain_destroy(blockchain_t* blockchain) {
    if (!blockchain) return;
    
    pthread_rwlock_wrlock(&blockchain->chain_lock);
    
    /* Free all blocks */
    for (uint64_t i = 0; i < blockchain->height; i++) {
        if (blockchain->blocks[i]) {
            if (blockchain->blocks[i]->transactions) {
                for (uint32_t j = 0; j < blockchain->blocks[i]->tx_count; j++) {
                    free(blockchain->blocks[i]->transactions[j]);
                }
                free(blockchain->blocks[i]->transactions);
            }
            free(blockchain->blocks[i]);
        }
    }
    
    free(blockchain->blocks);
    pthread_rwlock_unlock(&blockchain->chain_lock);
    pthread_rwlock_destroy(&blockchain->chain_lock);
    free(blockchain);
}

/* Create aggregator node */
node_t* cmptr_blockchain_create_aggregator(
    blockchain_t* blockchain,
    uint32_t aggregator_id
) {
    if (!blockchain || aggregator_id >= 1000) return NULL;
    
    node_t* node = calloc(1, sizeof(node_t));
    if (!node) return NULL;
    
    node->type = NODE_TYPE_AGGREGATOR;
    node->state = NODE_STATE_INITIALIZING;
    node->blockchain = blockchain;
    
    /* Initialize aggregator */
    blockchain_aggregator_t* agg = &node->data.aggregator;
    agg->id = aggregator_id;
    agg->tps_limit = 1000;  /* 1000 TPS per aggregator */
    agg->transactions_processed = 0;
    agg->current_batch_size = 0;
    pthread_mutex_init(&agg->batch_mutex, NULL);
    agg->batch_capacity = 10000;  /* Can batch up to 10k transactions */
    agg->pending_batch = calloc(agg->batch_capacity, sizeof(transaction_t*));
    
    /* Initialize accumulator */
    node->accumulator = cmptr_accumulator_init();
    
    /* Set storage config for aggregator (light) */
    node->storage_config = cmptr_blockchain_storage_config_light();
    
    /* Network config */
    node->network_config.port = 8333 + aggregator_id;
    node->network_config.max_peers = 50;
    node->network_config.target_outbound = 8;
    
    printf("Created Aggregator Node #%u (Port: %u)\n", 
           aggregator_id, node->network_config.port);
    
    return node;
}

/* Create generator node */
node_t* cmptr_blockchain_create_generator(
    blockchain_t* blockchain,
    uint32_t generator_id,
    uint32_t aggregator_start_id
) {
    if (!blockchain || generator_id >= 100) return NULL;
    
    node_t* node = calloc(1, sizeof(node_t));
    if (!node) return NULL;
    
    node->type = NODE_TYPE_GENERATOR;
    node->state = NODE_STATE_INITIALIZING;
    node->blockchain = blockchain;
    
    /* Initialize generator */
    generator_t* gen = &node->data.generator;
    gen->id = generator_id;
    gen->proofs_generated = 0;
    gen->is_generating = false;
    
    /* Note: In a real implementation, we'd connect to actual aggregator nodes */
    for (int i = 0; i < 10; i++) {
        gen->aggregators[i] = NULL;  /* Would be actual aggregator connections */
    }
    
    /* Initialize accumulator */
    node->accumulator = cmptr_accumulator_init();
    
    /* Set storage config for generator (full) */
    node->storage_config = cmptr_blockchain_storage_config_full();
    
    /* Network config */
    node->network_config.port = 9333 + generator_id;
    node->network_config.max_peers = 100;
    node->network_config.target_outbound = 20;
    
    printf("Created Generator Node #%u (Port: %u)\n", 
           generator_id, node->network_config.port);
    
    return node;
}

/* Create producer node */
node_t* cmptr_blockchain_create_producer(
    blockchain_t* blockchain,
    uint32_t producer_id,
    uint32_t generator_start_id
) {
    if (!blockchain || producer_id >= 10) return NULL;
    
    node_t* node = calloc(1, sizeof(node_t));
    if (!node) return NULL;
    
    node->type = NODE_TYPE_PRODUCER;
    node->state = NODE_STATE_INITIALIZING;
    node->blockchain = blockchain;
    
    /* Initialize producer */
    producer_t* prod = &node->data.producer;
    prod->id = producer_id;
    prod->blocks_produced = 0;
    prod->current_block = NULL;
    pthread_mutex_init(&prod->block_mutex, NULL);
    
    /* Note: In a real implementation, we'd connect to actual generator nodes */
    for (int i = 0; i < 10; i++) {
        prod->generators[i] = NULL;  /* Would be actual generator connections */
    }
    
    /* Initialize accumulator */
    node->accumulator = cmptr_accumulator_init();
    
    /* Set storage config for producer (archive) */
    node->storage_config = cmptr_blockchain_storage_config_archive();
    
    /* Network config */
    node->network_config.port = 10333 + producer_id;
    node->network_config.max_peers = 200;
    node->network_config.target_outbound = 50;
    
    /* Consensus config */
    node->consensus_config.block_time_ms = 10000;  /* 10 second blocks */
    node->consensus_config.pow_difficulty = 20;
    node->consensus_config.min_validators = 100;
    node->consensus_config.pruning_interval = 86400;  /* Daily pruning */
    
    printf("Created Producer Node #%u (Port: %u)\n", 
           producer_id, node->network_config.port);
    
    return node;
}

/* Create validator node */
node_t* cmptr_blockchain_create_validator(blockchain_t* blockchain) {
    if (!blockchain) return NULL;
    
    node_t* node = calloc(1, sizeof(node_t));
    if (!node) return NULL;
    
    node->type = NODE_TYPE_VALIDATOR;
    node->state = NODE_STATE_INITIALIZING;
    node->blockchain = blockchain;
    
    /* Initialize validator */
    validator_t* val = &node->data.validator;
    val->blocks_validated = 0;
    val->last_validated_height = 0;
    memset(val->accumulator_root, 0, 32);
    
    /* Validators don't need full accumulator, just verify proofs */
    node->accumulator = NULL;
    
    /* Set storage config for validator (ultra-light) */
    node->storage_config = cmptr_blockchain_storage_config_ultralight();
    
    /* Network config */
    static uint32_t validator_count = 0;
    node->network_config.port = 11333 + (validator_count++);
    node->network_config.max_peers = 20;
    node->network_config.target_outbound = 5;
    
    printf("Created Validator Node (Port: %u)\n", node->network_config.port);
    
    return node;
}

/* Start node */
bool cmptr_blockchain_start_node(node_t* node) {
    if (!node || node->state != NODE_STATE_INITIALIZING) {
        return false;
    }
    
    /* Initialize networking */
    network_manager_t* net = network_init(node, node->network_config.port);
    if (!net) {
        return false;
    }
    
    /* Start network thread */
    if (!network_start(net)) {
        network_destroy(net);
        return false;
    }
    
    /* Node-specific initialization */
    switch (node->type) {
        case NODE_TYPE_AGGREGATOR:
            printf("Starting Aggregator #%u...\n", node->data.aggregator.id);
            break;
            
        case NODE_TYPE_GENERATOR:
            printf("Starting Generator #%u...\n", node->data.generator.id);
            /* Would start proof generation threads here */
            break;
            
        case NODE_TYPE_PRODUCER:
            printf("Starting Producer #%u...\n", node->data.producer.id);
            /* Would start block production timer here */
            break;
            
        case NODE_TYPE_VALIDATOR:
            printf("Starting Validator...\n");
            break;
            
        default:
            break;
    }
    
    node->state = NODE_STATE_SYNCING;
    
    /* Begin synchronization */
    /* In real implementation, would sync from peers */
    node->state = NODE_STATE_ACTIVE;
    
    return true;
}

/* Submit transaction to aggregator */
bool cmptr_blockchain_submit_transaction(
    node_t* aggregator_node,
    const transaction_t* tx
) {
    if (!aggregator_node || !tx || 
        aggregator_node->type != NODE_TYPE_AGGREGATOR) {
        return false;
    }
    
    blockchain_aggregator_t* agg = &aggregator_node->data.aggregator;
    
    pthread_mutex_lock(&agg->batch_mutex);
    
    /* Check rate limit */
    if (agg->current_batch_size >= agg->batch_capacity) {
        pthread_mutex_unlock(&agg->batch_mutex);
        return false;  /* Batch full */
    }
    
    /* Add to batch */
    transaction_t* tx_copy = malloc(sizeof(transaction_t));
    memcpy(tx_copy, tx, sizeof(transaction_t));
    
    agg->pending_batch[agg->current_batch_size++] = tx_copy;
    agg->transactions_processed++;
    
    pthread_mutex_unlock(&agg->batch_mutex);
    
    /* Update blockchain metrics */
    aggregator_node->blockchain->total_transactions++;
    
    return true;
}

/* Get block by height */
block_t* cmptr_blockchain_get_block(
    const blockchain_t* blockchain,
    uint64_t height
) {
    if (!blockchain || height >= blockchain->height) {
        return NULL;
    }
    
    pthread_rwlock_rdlock((pthread_rwlock_t*)&blockchain->chain_lock);
    block_t* block = blockchain->blocks[height];
    pthread_rwlock_unlock((pthread_rwlock_t*)&blockchain->chain_lock);
    
    return block;
}

/* Add block to chain */
bool cmptr_blockchain_add_block(
    blockchain_t* blockchain,
    const block_t* block
) {
    if (!blockchain || !block) return false;
    
    pthread_rwlock_wrlock(&blockchain->chain_lock);
    
    /* Verify block height */
    if (block->height != blockchain->height) {
        pthread_rwlock_unlock(&blockchain->chain_lock);
        return false;
    }
    
    /* Verify previous hash */
    if (blockchain->height > 0) {
        uint8_t prev_hash[32];
        block_t* prev = blockchain->blocks[blockchain->height - 1];
        
        /* Calculate hash of previous block */
        sha3_256((uint8_t*)prev, sizeof(block_t), prev_hash);
        
        if (memcmp(block->prev_hash, prev_hash, 32) != 0) {
            pthread_rwlock_unlock(&blockchain->chain_lock);
            return false;
        }
    }
    
    /* Allocate more space if needed */
    if (blockchain->height >= 10000) {
        /* In real implementation, would resize dynamically */
    }
    
    /* Copy block */
    block_t* block_copy = malloc(sizeof(block_t));
    memcpy(block_copy, block, sizeof(block_t));
    
    /* Copy transactions */
    if (block->tx_count > 0) {
        block_copy->transactions = calloc(block->tx_count, sizeof(transaction_t*));
        for (uint32_t i = 0; i < block->tx_count; i++) {
            block_copy->transactions[i] = malloc(sizeof(transaction_t));
            memcpy(block_copy->transactions[i], block->transactions[i], 
                   sizeof(transaction_t));
        }
    }
    
    /* Add to chain */
    blockchain->blocks[blockchain->height++] = block_copy;
    blockchain->total_transactions += block->tx_count;
    
    /* Update metrics */
    if (blockchain->height > 1) {
        uint64_t time_diff = block->timestamp - 
                            blockchain->blocks[blockchain->height-2]->timestamp;
        if (time_diff > 0) {
            blockchain->current_tps = (double)(block->tx_count * 1000000) / time_diff;
        }
    }
    
    pthread_rwlock_unlock(&blockchain->chain_lock);
    
    printf("Added block #%lu with %u transactions (%.1f TPS)\n",
           block->height, block->tx_count, blockchain->current_tps);
    
    return true;
}

/* Get blockchain metrics */
blockchain_metrics_t cmptr_blockchain_get_metrics(
    const blockchain_t* blockchain
) {
    blockchain_metrics_t metrics = {0};
    
    if (!blockchain) return metrics;
    
    pthread_rwlock_rdlock((pthread_rwlock_t*)&blockchain->chain_lock);
    
    metrics.total_transactions = blockchain->total_transactions;
    metrics.current_tps = blockchain->current_tps;
    metrics.blockchain_height = blockchain->height;
    metrics.storage_used_gb = blockchain->storage_used_bytes / (1024.0 * 1024.0 * 1024.0);
    metrics.nullifiers_pruned = blockchain->total_pruned;
    
    /* Calculate average block time */
    if (blockchain->height > 10) {
        uint64_t total_time = 0;
        for (uint64_t i = blockchain->height - 10; i < blockchain->height - 1; i++) {
            total_time += blockchain->blocks[i+1]->timestamp - 
                         blockchain->blocks[i]->timestamp;
        }
        metrics.avg_block_time_ms = (double)total_time / (9 * 1000);
    }
    
    pthread_rwlock_unlock((pthread_rwlock_t*)&blockchain->chain_lock);
    
    return metrics;
}

/* Storage configuration presets */
storage_config_t cmptr_blockchain_storage_config_archive(void) {
    return (storage_config_t){
        .retention_days = 0,  /* Keep forever */
        .store_transactions = true,
        .store_proofs = true,
        .store_witnesses = true,
        .max_storage_gb = 0  /* Unlimited */
    };
}

storage_config_t cmptr_blockchain_storage_config_full(void) {
    return (storage_config_t){
        .retention_days = 365,  /* 1 year */
        .store_transactions = true,
        .store_proofs = true,
        .store_witnesses = false,
        .max_storage_gb = 100
    };
}

storage_config_t cmptr_blockchain_storage_config_light(void) {
    return (storage_config_t){
        .retention_days = 30,  /* 1 month */
        .store_transactions = true,
        .store_proofs = false,
        .store_witnesses = false,
        .max_storage_gb = 10
    };
}

storage_config_t cmptr_blockchain_storage_config_ultralight(void) {
    return (storage_config_t){
        .retention_days = 1,  /* 1 day */
        .store_transactions = false,
        .store_proofs = false,
        .store_witnesses = false,
        .max_storage_gb = 1
    };
}