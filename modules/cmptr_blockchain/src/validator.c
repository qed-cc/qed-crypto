/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>
#include <string.h>

/* Validate block */
bool validator_validate_block(
    node_t* node,
    const block_t* block
) {
    if (!node || !block || node->type != NODE_TYPE_VALIDATOR) {
        return false;
    }
    
    validator_t* val = &node->data.validator;
    
    /* Check basic validity */
    if (block->height != val->last_validated_height + 1) {
        printf("Validator: Invalid block height %lu (expected %lu)\n",
               block->height, val->last_validated_height + 1);
        return false;
    }
    
    /* In real implementation:
     * 1. Verify PoW
     * 2. Verify recursive proofs
     * 3. Verify nullifier/kernel proofs
     * 4. Check consensus rules
     */
    
    /* Update validator state */
    val->last_validated_height = block->height;
    val->blocks_validated++;
    
    /* Update accumulator root from block proof */
    /* In real implementation, extract from recursive proof */
    memset(val->accumulator_root, 0, 32);
    
    printf("Validator: Validated block #%lu\n", block->height);
    
    return true;
}

/* Validator sync */
bool validator_sync(node_t* node) {
    if (!node || node->type != NODE_TYPE_VALIDATOR) {
        return false;
    }
    
    validator_t* val = &node->data.validator;
    
    /* Get current chain height */
    uint64_t chain_height = node->blockchain->height;
    
    /* Validate all blocks we haven't seen */
    while (val->last_validated_height < chain_height - 1) {
        block_t* block = cmptr_blockchain_get_block(
            node->blockchain,
            val->last_validated_height + 1
        );
        
        if (!block) {
            printf("Validator: Failed to get block #%lu\n",
                   val->last_validated_height + 1);
            return false;
        }
        
        if (!validator_validate_block(node, block)) {
            printf("Validator: Block #%lu validation failed\n", block->height);
            return false;
        }
    }
    
    printf("Validator: Synced to height %lu\n", val->last_validated_height);
    return true;
}

/* Get validator state proof */
bool validator_get_state_proof(
    const node_t* node,
    uint8_t* proof_out,
    size_t* proof_size
) {
    if (!node || !proof_out || !proof_size || 
        node->type != NODE_TYPE_VALIDATOR) {
        return false;
    }
    
    const validator_t* val = &node->data.validator;
    
    /* In real implementation:
     * - Return compact proof of current accumulator state
     * - Include block height and accumulator root
     * - This allows light clients to verify state
     */
    
    /* For now, just return accumulator root */
    memcpy(proof_out, val->accumulator_root, 32);
    *proof_size = 32;
    
    return true;
}