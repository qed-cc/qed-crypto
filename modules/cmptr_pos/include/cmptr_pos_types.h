/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_TYPES_H
#define CMPTR_POS_TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Validator stake states */
typedef enum {
    STAKE_STATE_INACTIVE,     /* Not staking */
    STAKE_STATE_PENDING,      /* Waiting to join */
    STAKE_STATE_ACTIVE,       /* Actively validating */
    STAKE_STATE_UNBONDING,    /* Withdrawing stake */
    STAKE_STATE_SLASHED       /* Punished for misbehavior */
} stake_state_t;

/* Consensus phases */
typedef enum {
    PHASE_IDLE,
    PHASE_STAKE_SNAPSHOT,     /* Take stake snapshot */
    PHASE_VRF_ELECTION,       /* Committee election */
    PHASE_DAG_CONSTRUCTION,   /* Build Narwhal DAG */
    PHASE_ORDERING,           /* Mysticeti/Bullshark ordering */
    PHASE_STARK_GENERATION,   /* Generate recursive proof */
    PHASE_FINALIZATION       /* Finalize block */
} consensus_phase_t;

/* Validator information */
typedef struct validator_pos {
    uint8_t public_key[32];        /* Validator identity */
    uint64_t stake_amount;         /* Amount staked */
    stake_state_t state;           /* Current stake state */
    uint64_t activation_epoch;     /* When validator joined */
    uint64_t exit_epoch;           /* When validator left */
    
    /* VRF credentials */
    uint8_t vrf_public_key[64];    /* Lattice public key */
    uint8_t vrf_private_key[256];  /* Lattice private key */
    
    /* Performance metrics */
    uint64_t blocks_proposed;
    uint64_t blocks_signed;
    uint64_t blocks_missed;
    double uptime_percentage;
} validator_pos_t;

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_POS_TYPES_H */