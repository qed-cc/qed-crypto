/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Committee selection logic is in lattice_vrf.c */
/* This file is for additional committee management */

/* Free committee */
void cmptr_pos_free_committee(committee_t* committee) {
    if (!committee) {
        return;
    }
    
    if (committee->members) {
        free(committee->members);
    }
    free(committee);
}

/* Get committee member by index */
validator_pos_t* cmptr_pos_get_committee_member(
    const committee_t* committee,
    uint32_t index
) {
    if (!committee || index >= committee->size) {
        return NULL;
    }
    
    return committee->members[index];
}

/* Check if validator is in committee */
bool cmptr_pos_is_in_committee(
    const committee_t* committee,
    const uint8_t* public_key
) {
    if (!committee || !public_key) {
        return false;
    }
    
    for (uint32_t i = 0; i < committee->size; i++) {
        if (memcmp(committee->members[i]->public_key, public_key, 32) == 0) {
            return true;
        }
    }
    
    return false;
}

/* Calculate committee stats */
void cmptr_pos_committee_stats(
    const committee_t* committee,
    uint64_t* total_stake_out,
    uint64_t* min_stake_out,
    uint64_t* max_stake_out
) {
    if (!committee || committee->size == 0) {
        return;
    }
    
    uint64_t total = 0;
    uint64_t min_stake = UINT64_MAX;
    uint64_t max_stake = 0;
    
    for (uint32_t i = 0; i < committee->size; i++) {
        uint64_t stake = committee->members[i]->stake_amount;
        total += stake;
        
        if (stake < min_stake) {
            min_stake = stake;
        }
        if (stake > max_stake) {
            max_stake = stake;
        }
    }
    
    if (total_stake_out) {
        *total_stake_out = total;
    }
    if (min_stake_out) {
        *min_stake_out = min_stake;
    }
    if (max_stake_out) {
        *max_stake_out = max_stake;
    }
}