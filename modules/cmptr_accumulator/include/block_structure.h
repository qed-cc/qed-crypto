/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef BLOCK_STRUCTURE_H
#define BLOCK_STRUCTURE_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declaration */
struct cmptr_accumulator;

/* Block header with PoW and timestamp */
typedef struct {
    /* Block identification */
    uint64_t height;                     /* Block number */
    uint8_t prev_hash[32];               /* SHA3 of previous block */
    uint64_t timestamp;                  /* Unix timestamp (microseconds) */
    
    /* Proof of Work */
    uint8_t nonce[32];                   /* PoW nonce */
    uint32_t difficulty;                 /* Required leading zeros */
    uint8_t pow_hash[32];                /* SHA3(prev_hash || timestamp || merkle_root || nonce) */
    
    /* State commitments */
    uint8_t nullifier_root[32];          /* Merkle root of nullifier accumulator */
    uint8_t kernel_root[32];             /* Merkle root of kernel accumulator */
    uint8_t pruning_root[32];            /* Root of pruning history */
    
    /* Transaction data */
    uint32_t tx_count;                   /* Number of transactions */
    uint8_t tx_merkle_root[32];          /* Merkle root of transactions */
    
    /* Recursive proof */
    uint8_t recursive_proof[190*1024];   /* Proves all previous blocks valid */
    uint32_t proof_size;                 /* Actual proof size */
} block_header_t;

/* Block with transactions */
typedef struct {
    block_header_t header;
    /* Transactions are stored separately for efficiency */
    uint8_t* transactions;               /* Serialized transaction data */
    uint32_t transactions_size;
} block_t;

/* Block validation result */
typedef struct {
    bool valid;
    bool pow_valid;
    bool timestamp_valid;
    bool proof_valid;
    bool transactions_valid;
    char error_message[256];
} block_validation_t;

/* PoW mining context */
typedef struct {
    uint8_t prev_hash[32];
    uint64_t timestamp;
    uint8_t merkle_root[32];
    uint32_t difficulty;
    
    /* Mining state */
    uint8_t best_nonce[32];
    uint8_t best_hash[32];
    uint32_t best_zeros;
    uint64_t hashes_tried;
    
    /* For parallel mining */
    volatile bool solution_found;
    pthread_mutex_t mutex;
} mining_context_t;

/* Chain state for recursive proofs */
typedef struct {
    uint64_t total_work;                 /* Cumulative PoW difficulty */
    uint64_t chain_length;               /* Number of blocks */
    uint8_t genesis_hash[32];            /* Hash of genesis block */
    uint8_t latest_hash[32];             /* Hash of latest block */
    
    /* Recursive proof that validates entire chain */
    uint8_t chain_proof[190*1024];
    uint32_t chain_proof_size;
} chain_state_t;

/* Functions for block operations */
block_t* create_genesis_block(uint64_t timestamp);

block_t* create_block(
    const block_t* prev_block,
    const uint8_t transactions[],
    uint32_t tx_size,
    uint64_t timestamp
);

/* Mining functions */
mining_context_t* create_mining_context(
    const block_t* prev_block,
    const uint8_t tx_merkle_root[32],
    uint64_t timestamp,
    uint32_t difficulty
);

bool mine_block_pow(
    mining_context_t* ctx,
    block_header_t* header,
    uint64_t max_attempts
);

void mine_block_parallel(
    mining_context_t* ctx,
    block_header_t* header,
    uint32_t num_threads
);

/* Validation */
block_validation_t validate_block(
    const block_t* block,
    const block_t* prev_block,
    const chain_state_t* chain
);

bool validate_pow(
    const block_header_t* header,
    uint32_t required_difficulty
);

bool validate_timestamp(
    const block_header_t* header,
    const block_header_t* prev_header
);

/* Difficulty adjustment */
uint32_t calculate_next_difficulty(
    const block_header_t* current,
    const block_header_t* prev,
    uint64_t target_block_time_us
);

/* Chain operations */
chain_state_t* create_chain_state(const block_t* genesis);

bool update_chain_state(
    chain_state_t* chain,
    const block_t* new_block
);

/* Recursive proof generation for blocks */
bool generate_block_proof(
    block_t* block,
    const chain_state_t* chain,
    const struct cmptr_accumulator* acc
);

/* Serialization */
size_t serialize_block(
    const block_t* block,
    uint8_t* buffer,
    size_t buffer_size
);

block_t* deserialize_block(
    const uint8_t* buffer,
    size_t buffer_size
);

/* Helper functions */
uint32_t count_leading_zeros(const uint8_t hash[32]);
void print_block_header(const block_header_t* header);
double calculate_hash_rate(uint64_t hashes, uint64_t time_us);

#ifdef __cplusplus
}
#endif

#endif /* BLOCK_STRUCTURE_H */