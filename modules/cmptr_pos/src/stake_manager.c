/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Remove validator */
bool cmptr_pos_remove_validator(
    pos_state_t* pos,
    const uint8_t* public_key
) {
    if (!pos || !public_key) {
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Find validator */
    validator_pos_t* validator = NULL;
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (memcmp(pos->validators[i]->public_key, public_key, 32) == 0) {
            validator = pos->validators[i];
            break;
        }
    }
    
    if (!validator) {
        pthread_mutex_unlock(&pos->state_mutex);
        fprintf(stderr, "Validator not found\n");
        return false;
    }
    
    /* Check if already exiting */
    if (validator->state == STAKE_STATE_UNBONDING ||
        validator->state == STAKE_STATE_INACTIVE) {
        pthread_mutex_unlock(&pos->state_mutex);
        return true; /* Already exiting */
    }
    
    /* Start unbonding */
    validator->state = STAKE_STATE_UNBONDING;
    validator->exit_epoch = pos->current_epoch + pos->unbonding_period;
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Validator entering unbonding period (exit epoch: %lu)\n",
           validator->exit_epoch);
    return true;
}

/* Update stake */
bool cmptr_pos_update_stake(
    pos_state_t* pos,
    const uint8_t* public_key,
    uint64_t new_stake
) {
    if (!pos || !public_key) {
        return false;
    }
    
    /* Check minimum */
    if (new_stake < pos->min_stake) {
        fprintf(stderr, "New stake below minimum: %lu < %lu\n",
                new_stake, pos->min_stake);
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Find validator */
    validator_pos_t* validator = NULL;
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (memcmp(pos->validators[i]->public_key, public_key, 32) == 0) {
            validator = pos->validators[i];
            break;
        }
    }
    
    if (!validator) {
        pthread_mutex_unlock(&pos->state_mutex);
        fprintf(stderr, "Validator not found\n");
        return false;
    }
    
    /* Check state */
    if (validator->state != STAKE_STATE_ACTIVE &&
        validator->state != STAKE_STATE_PENDING) {
        pthread_mutex_unlock(&pos->state_mutex);
        fprintf(stderr, "Cannot update stake in state: %d\n", validator->state);
        return false;
    }
    
    /* Update stake */
    uint64_t old_stake = validator->stake_amount;
    validator->stake_amount = new_stake;
    pos->total_staked = pos->total_staked - old_stake + new_stake;
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Updated stake: %lu → %lu\n", old_stake, new_stake);
    return true;
}

/* Advance epoch */
bool cmptr_pos_advance_epoch(pos_state_t* pos) {
    if (!pos) {
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    pos->current_epoch++;
    
    /* Process validator state changes */
    uint32_t activated = 0;
    uint32_t exited = 0;
    
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        validator_pos_t* val = pos->validators[i];
        
        /* Activate pending validators */
        if (val->state == STAKE_STATE_PENDING &&
            val->activation_epoch <= pos->current_epoch) {
            val->state = STAKE_STATE_ACTIVE;
            activated++;
        }
        
        /* Process exits */
        if (val->state == STAKE_STATE_UNBONDING &&
            val->exit_epoch <= pos->current_epoch) {
            val->state = STAKE_STATE_INACTIVE;
            pos->total_staked -= val->stake_amount;
            exited++;
        }
    }
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Advanced to epoch %u (activated: %u, exited: %u)\n",
           pos->current_epoch, activated, exited);
    
    return true;
}

/* Take stake snapshot */
stake_snapshot_t* cmptr_pos_take_snapshot(pos_state_t* pos) {
    if (!pos) {
        return NULL;
    }
    
    stake_snapshot_t* snapshot = calloc(1, sizeof(stake_snapshot_t));
    if (!snapshot) {
        return NULL;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Count active validators */
    uint32_t active_count = 0;
    uint64_t total_active_stake = 0;
    
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (pos->validators[i]->state == STAKE_STATE_ACTIVE) {
            active_count++;
            total_active_stake += pos->validators[i]->stake_amount;
        }
    }
    
    /* Create snapshot (simplified - would use Verkle tree) */
    verkle_commitment_t* commitment = calloc(1, sizeof(verkle_commitment_t));
    
    /* Generate deterministic root based on validator set */
    uint8_t snapshot_data[32] = {0};
    memcpy(snapshot_data, &pos->current_epoch, 4);
    memcpy(snapshot_data + 4, &active_count, 4);
    memcpy(snapshot_data + 8, &total_active_stake, 8);
    
    /* In real implementation: build Verkle tree and compute root */
    memcpy(commitment->root, snapshot_data, 32);
    commitment->height = 20; /* log2(1M validators) */
    commitment->total_stake = total_active_stake;
    commitment->validator_count = active_count;
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    printf("✓ Stake snapshot taken:\n");
    printf("  - Active validators: %u\n", active_count);
    printf("  - Total stake: %lu\n", total_active_stake);
    printf("  - Verkle root: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", commitment->root[i]);
    }
    printf("...\n");
    
    return (stake_snapshot_t*)commitment;
}

/* Report equivocation */
bool cmptr_pos_report_equivocation(
    pos_state_t* pos,
    const uint8_t* validator_key,
    const uint8_t* evidence,
    size_t evidence_size
) {
    if (!pos || !validator_key || !evidence) {
        return false;
    }
    
    pthread_mutex_lock(&pos->state_mutex);
    
    /* Find validator */
    validator_pos_t* validator = NULL;
    for (uint32_t i = 0; i < pos->validator_count; i++) {
        if (memcmp(pos->validators[i]->public_key, validator_key, 32) == 0) {
            validator = pos->validators[i];
            break;
        }
    }
    
    if (!validator) {
        pthread_mutex_unlock(&pos->state_mutex);
        return false;
    }
    
    /* In real implementation: verify evidence */
    if (evidence_size < 64) {
        pthread_mutex_unlock(&pos->state_mutex);
        return false;
    }
    
    /* Slash validator */
    if (validator->state == STAKE_STATE_ACTIVE) {
        validator->state = STAKE_STATE_SLASHED;
        pos->total_staked -= validator->stake_amount;
        
        printf("⚠️  Validator slashed for equivocation!\n");
        printf("   - Stake forfeited: %lu\n", validator->stake_amount);
    }
    
    pthread_mutex_unlock(&pos->state_mutex);
    
    return true;
}

/* Report invalid block */
bool cmptr_pos_report_invalid_block(
    pos_state_t* pos,
    const uint8_t* validator_key,
    const block_t* invalid_block
) {
    if (!pos || !validator_key || !invalid_block) {
        return false;
    }
    
    /* Similar to equivocation - verify and slash */
    return cmptr_pos_report_equivocation(pos, validator_key, 
                                       (uint8_t*)invalid_block, 
                                       sizeof(block_t));
}