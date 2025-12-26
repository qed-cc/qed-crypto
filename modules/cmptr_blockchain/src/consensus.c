/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "consensus.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Initialize consensus */
consensus_state_t* consensus_init(fork_choice_rule_t fork_rule) {
    consensus_state_t* consensus = calloc(1, sizeof(consensus_state_t));
    if (!consensus) return NULL;
    
    consensus->current_epoch = 0;
    consensus->epoch_start_time = 0;
    consensus->active_producers = 10;  /* 10 producers in network */
    consensus->required_confirmations = 6;
    
    consensus->main_chain_height = 0;
    consensus->reorganization_count = 0;
    
    consensus->current_difficulty = 20;  /* Initial difficulty */
    consensus->last_adjustment_time = 0;
    consensus->blocks_since_adjustment = 0;
    consensus->average_block_time = 10.0;  /* 10 seconds target */
    
    return consensus;
}

/* Destroy consensus */
void consensus_destroy(consensus_state_t* consensus) {
    free(consensus);
}

/* Validate block */
validation_result_t consensus_validate_block(
    const consensus_state_t* consensus,
    const block_t* block,
    const block_t* parent
) {
    validation_result_t result = {
        .is_valid = true,
        .pow_valid = true,
        .timestamp_valid = true,
        .transactions_valid = true,
        .proofs_valid = true,
        .producer_authorized = true,
        .rejection_reason = ""
    };
    
    /* Check timestamp */
    if (parent && block->timestamp <= parent->timestamp) {
        result.is_valid = false;
        result.timestamp_valid = false;
        snprintf(result.rejection_reason, 256, 
                "Block timestamp not greater than parent");
        return result;
    }
    
    /* Check producer authorization */
    if (block->producer_id >= consensus->active_producers) {
        result.is_valid = false;
        result.producer_authorized = false;
        snprintf(result.rejection_reason, 256,
                "Invalid producer ID: %u", block->producer_id);
        return result;
    }
    
    /* In real implementation:
     * - Verify PoW meets difficulty
     * - Verify all recursive proofs
     * - Check transaction validity
     * - Verify state transitions
     */
    
    return result;
}

/* Calculate next difficulty */
uint32_t consensus_calculate_difficulty(
    const consensus_state_t* consensus,
    const block_t* last_block,
    uint64_t target_time_ms
) {
    /* Simple difficulty adjustment */
    uint32_t new_difficulty = consensus->current_difficulty;
    
    if (consensus->blocks_since_adjustment >= 100) {
        /* Adjust every 100 blocks */
        double actual_time = consensus->average_block_time * 1000;  /* ms */
        
        if (actual_time < target_time_ms * 0.5) {
            /* Too fast, increase difficulty */
            new_difficulty++;
        } else if (actual_time > target_time_ms * 2.0) {
            /* Too slow, decrease difficulty */
            if (new_difficulty > 10) {
                new_difficulty--;
            }
        }
    }
    
    return new_difficulty;
}

/* Get next producer */
uint32_t consensus_get_next_producer(
    const consensus_state_t* consensus,
    uint64_t block_height
) {
    /* Simple round-robin for now */
    return (uint32_t)(block_height % consensus->active_producers);
}

/* Check if block is finalized */
bool consensus_is_finalized(
    const consensus_state_t* consensus,
    uint64_t block_height
) {
    /* Block is finalized after required confirmations */
    return (consensus->main_chain_height - block_height) >= 
           consensus->required_confirmations;
}

/* Get consensus metrics */
consensus_metrics_t consensus_get_metrics(const consensus_state_t* consensus) {
    consensus_metrics_t metrics = {
        .blocks_per_second = 1.0 / consensus->average_block_time,
        .average_block_size = 190 * 1024,  /* ~190KB with proofs */
        .average_tx_per_block = 100000,  /* 100k tx per block */
        .uncle_rate = 0,  /* No uncles in this design */
        .reorg_depth_max = 0,
        .total_difficulty = consensus->current_difficulty * consensus->main_chain_height
    };
    
    return metrics;
}