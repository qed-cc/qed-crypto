/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_CONSENSUS_H
#define CMPTR_CONSENSUS_H

#include <stdint.h>
#include <stdbool.h>
#include "cmptr_blockchain.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Consensus state */
typedef struct {
    uint64_t current_epoch;
    uint64_t epoch_start_time;
    uint32_t active_producers;
    uint32_t required_confirmations;
    
    /* Fork detection */
    uint8_t main_chain_tip[32];
    uint64_t main_chain_height;
    uint32_t reorganization_count;
    
    /* Difficulty adjustment */
    uint32_t current_difficulty;
    uint64_t last_adjustment_time;
    uint64_t blocks_since_adjustment;
    double average_block_time;
} consensus_state_t;

/* Block validation result */
typedef struct {
    bool is_valid;
    bool pow_valid;
    bool timestamp_valid;
    bool transactions_valid;
    bool proofs_valid;
    bool producer_authorized;
    char rejection_reason[256];
} validation_result_t;

/* Fork choice rule */
typedef enum {
    FORK_CHOICE_LONGEST_CHAIN,      /* Simple longest chain */
    FORK_CHOICE_MOST_WORK,          /* Most accumulated PoW */
    FORK_CHOICE_RECURSIVE_WEIGHT    /* Weight by recursive proof depth */
} fork_choice_rule_t;

/* Initialize consensus */
consensus_state_t* consensus_init(
    fork_choice_rule_t fork_rule
);

void consensus_destroy(consensus_state_t* consensus);

/* Block validation */
validation_result_t consensus_validate_block(
    const consensus_state_t* consensus,
    const block_t* block,
    const block_t* parent
);

/* Proof of Work */
bool consensus_verify_pow(
    const block_t* block,
    uint32_t required_difficulty
);

uint32_t consensus_calculate_difficulty(
    const consensus_state_t* consensus,
    const block_t* last_block,
    uint64_t target_time_ms
);

/* Producer selection */
bool consensus_is_authorized_producer(
    const consensus_state_t* consensus,
    uint32_t producer_id,
    uint64_t block_height
);

uint32_t consensus_get_next_producer(
    const consensus_state_t* consensus,
    uint64_t block_height
);

/* Fork handling */
bool consensus_should_reorganize(
    const consensus_state_t* consensus,
    const block_t* current_tip,
    const block_t* competing_tip
);

uint64_t consensus_find_common_ancestor(
    const blockchain_t* blockchain,
    const block_t* block1,
    const block_t* block2
);

/* Finality */
bool consensus_is_finalized(
    const consensus_state_t* consensus,
    uint64_t block_height
);

uint64_t consensus_get_finalized_height(
    const consensus_state_t* consensus
);

/* Recursive proof verification */
bool consensus_verify_recursive_proofs(
    const block_t* block,
    const cmptr_accumulator_t* accumulator
);

/* Pruning consensus */
bool consensus_approve_pruning(
    const consensus_state_t* consensus,
    uint64_t prune_before_height,
    const uint8_t* pruning_proof,
    size_t proof_size
);

/* Network partition handling */
bool consensus_detect_partition(
    const consensus_state_t* consensus,
    uint32_t peer_count,
    uint64_t last_block_time
);

void consensus_handle_partition_recovery(
    consensus_state_t* consensus,
    blockchain_t* blockchain
);

/* Metrics */
typedef struct {
    double blocks_per_second;
    double average_block_size;
    double average_tx_per_block;
    uint32_t uncle_rate;  /* Orphaned blocks */
    uint32_t reorg_depth_max;
    uint64_t total_difficulty;
} consensus_metrics_t;

consensus_metrics_t consensus_get_metrics(
    const consensus_state_t* consensus
);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_CONSENSUS_H */