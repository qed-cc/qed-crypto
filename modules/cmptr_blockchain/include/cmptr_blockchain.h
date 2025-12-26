/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_BLOCKCHAIN_H
#define CMPTR_BLOCKCHAIN_H

#define _GNU_SOURCE  /* For pthread_rwlock_t */

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include <time.h>
#include "cmptr_accumulator.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct blockchain blockchain_t;
typedef struct node node_t;
typedef struct block block_t;
typedef struct transaction transaction_t;
typedef struct peer peer_t;

/* Node types in the hierarchy */
typedef enum {
    NODE_TYPE_AGGREGATOR,    /* Collects transactions, 1000 TPS */
    NODE_TYPE_GENERATOR,     /* Generates proofs for 100 aggregators */
    NODE_TYPE_PRODUCER,      /* Produces blocks from 10 generators */
    NODE_TYPE_VALIDATOR,     /* Lightweight validation only */
    NODE_TYPE_ARCHIVE,       /* Stores everything forever */
    NODE_TYPE_FULL,          /* Stores 1 year of data */
    NODE_TYPE_LIGHT,         /* Stores 1 month of data */
    NODE_TYPE_ULTRALIGHT     /* Stores only block headers */
} node_type_t;

/* Node state */
typedef enum {
    NODE_STATE_INITIALIZING,
    NODE_STATE_SYNCING,
    NODE_STATE_ACTIVE,
    NODE_STATE_SHUTTING_DOWN
} node_state_t;

/* Storage tier configuration */
typedef struct {
    uint64_t retention_days;      /* How long to keep data */
    bool store_transactions;      /* Store full transactions */
    bool store_proofs;           /* Store recursive proofs */
    bool store_witnesses;        /* Store witness data */
    uint64_t max_storage_gb;     /* Maximum storage to use */
} storage_config_t;

/* Network configuration */
typedef struct {
    uint16_t port;               /* P2P port */
    uint32_t max_peers;          /* Maximum peer connections */
    uint32_t target_outbound;    /* Target outbound connections */
    char bootstrap_nodes[10][256]; /* Bootstrap node addresses */
    uint32_t bootstrap_count;    /* Number of bootstrap nodes */
} network_config_t;

/* Consensus parameters */
typedef struct {
    uint32_t block_time_ms;      /* Target block time in milliseconds */
    uint32_t pow_difficulty;     /* Proof of work difficulty */
    uint32_t min_validators;     /* Minimum validators for consensus */
    uint64_t pruning_interval;   /* How often to prune (seconds) */
} consensus_config_t;

/* Aggregator node - collects transactions */
typedef struct {
    uint32_t id;                 /* Aggregator ID (0-999) */
    uint32_t tps_limit;          /* Transactions per second limit */
    uint64_t transactions_processed;
    uint64_t current_batch_size;
    pthread_mutex_t batch_mutex;
    transaction_t** pending_batch;
    uint32_t batch_capacity;
} blockchain_aggregator_t;

/* Generator node - creates proofs */
typedef struct {
    uint32_t id;                 /* Generator ID (0-99) */
    blockchain_aggregator_t* aggregators[10]; /* 10 aggregators per generator */
    uint64_t proofs_generated;
    pthread_t worker_threads[4]; /* Parallel proof generation */
    bool is_generating;
} generator_t;

/* Producer node - creates blocks */
typedef struct {
    uint32_t id;                 /* Producer ID (0-9) */
    generator_t* generators[10];  /* 10 generators per producer */
    uint64_t blocks_produced;
    block_t* current_block;
    pthread_mutex_t block_mutex;
} producer_t;

/* Validator node - lightweight verification */
typedef struct {
    uint64_t blocks_validated;
    uint64_t last_validated_height;
    uint8_t accumulator_root[32]; /* Current accumulator state */
} validator_t;

/* Main node structure */
struct node {
    node_type_t type;
    node_state_t state;
    
    /* Configuration */
    storage_config_t storage_config;
    network_config_t network_config;
    consensus_config_t consensus_config;
    
    /* Node-specific data */
    union {
        blockchain_aggregator_t aggregator;
        generator_t generator;
        producer_t producer;
        validator_t validator;
    } data;
    
    /* Blockchain reference */
    blockchain_t* blockchain;
    
    /* Networking */
    peer_t** peers;
    uint32_t peer_count;
    pthread_t network_thread;
    
    /* Accumulator integration */
    cmptr_accumulator_t* accumulator;
};

/* Block structure */
struct block {
    /* Header */
    uint64_t height;
    uint8_t prev_hash[32];
    uint8_t merkle_root[32];
    uint64_t timestamp;
    uint32_t nonce;
    uint32_t difficulty;
    
    /* Accumulator proofs */
    uint8_t nullifier_proof[190*1024];
    uint8_t kernel_proof[190*1024];
    uint8_t pruning_proof[190*1024];
    
    /* Transactions */
    transaction_t** transactions;
    uint32_t tx_count;
    
    /* Producer signature */
    uint32_t producer_id;
    uint8_t producer_signature[64];
};

/* Transaction structure */
struct transaction {
    uint8_t id[32];              /* Transaction hash */
    uint8_t nullifiers[2][32];   /* Input nullifiers */
    uint8_t commitments[2][32];  /* Output commitments */
    uint8_t proof[8192];         /* Zero-knowledge proof */
    uint64_t timestamp;
    uint32_t aggregator_id;      /* Which aggregator processed this */
};

/* Blockchain state */
struct blockchain {
    /* Chain data */
    block_t** blocks;
    uint64_t height;
    uint64_t total_transactions;
    
    /* Storage based on node type */
    uint64_t oldest_block_stored;
    uint64_t storage_used_bytes;
    
    /* Synchronization */
    pthread_rwlock_t chain_lock;
    bool is_syncing;
    uint64_t sync_target_height;
    
    /* Metrics */
    double current_tps;
    uint64_t total_pruned;
    uint64_t last_prune_time;
};

/* Peer information */
struct peer {
    char address[256];
    uint16_t port;
    node_type_t type;
    uint64_t last_seen;
    uint64_t latency_ms;
    bool is_outbound;
    pthread_t peer_thread;
    int socket_fd;
};

/* Initialize blockchain */
blockchain_t* cmptr_blockchain_init(void);
void cmptr_blockchain_destroy(blockchain_t* blockchain);

/* Create different node types */
node_t* cmptr_blockchain_create_aggregator(
    blockchain_t* blockchain,
    uint32_t aggregator_id
);

node_t* cmptr_blockchain_create_generator(
    blockchain_t* blockchain,
    uint32_t generator_id,
    uint32_t aggregator_start_id
);

node_t* cmptr_blockchain_create_producer(
    blockchain_t* blockchain,
    uint32_t producer_id,
    uint32_t generator_start_id
);

node_t* cmptr_blockchain_create_validator(
    blockchain_t* blockchain
);

/* Node lifecycle */
bool cmptr_blockchain_start_node(node_t* node);
bool cmptr_blockchain_stop_node(node_t* node);
node_state_t cmptr_blockchain_get_node_state(const node_t* node);

/* Transaction processing */
bool cmptr_blockchain_submit_transaction(
    node_t* aggregator_node,
    const transaction_t* tx
);

/* Block operations */
block_t* cmptr_blockchain_get_block(
    const blockchain_t* blockchain,
    uint64_t height
);

bool cmptr_blockchain_add_block(
    blockchain_t* blockchain,
    const block_t* block
);

/* Synchronization */
bool cmptr_blockchain_sync_from_peer(
    node_t* node,
    const char* peer_address,
    uint16_t peer_port
);

/* Storage management */
uint64_t cmptr_blockchain_prune_old_data(
    node_t* node
);

uint64_t cmptr_blockchain_get_storage_used(
    const node_t* node
);

/* Network operations */
bool cmptr_blockchain_connect_peer(
    node_t* node,
    const char* address,
    uint16_t port
);

bool cmptr_blockchain_disconnect_peer(
    node_t* node,
    const peer_t* peer
);

uint32_t cmptr_blockchain_get_peer_count(
    const node_t* node
);

/* Metrics and monitoring */
typedef struct {
    uint64_t total_transactions;
    double current_tps;
    uint64_t blockchain_height;
    uint64_t peers_connected;
    double storage_used_gb;
    uint64_t nullifiers_pruned;
    double avg_block_time_ms;
    uint32_t active_aggregators;
    uint32_t active_generators;
    uint32_t active_producers;
    uint32_t active_validators;
} blockchain_metrics_t;

blockchain_metrics_t cmptr_blockchain_get_metrics(
    const blockchain_t* blockchain
);

/* Configuration helpers */
storage_config_t cmptr_blockchain_storage_config_archive(void);
storage_config_t cmptr_blockchain_storage_config_full(void);
storage_config_t cmptr_blockchain_storage_config_light(void);
storage_config_t cmptr_blockchain_storage_config_ultralight(void);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_BLOCKCHAIN_H */