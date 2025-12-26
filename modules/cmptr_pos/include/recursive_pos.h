/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef RECURSIVE_POS_H
#define RECURSIVE_POS_H

#include "cmptr_pos.h"
#include "basefold_raa.h"
#include "circular_recursion.h"

/**
 * Recursive Proof of Stake Enhancements
 * =====================================
 * 
 * Leverages CMPTR's recursive proof capabilities to dramatically
 * improve PoS performance, security, and scalability.
 */

/* Recursive committee proof - aggregates all VRF proofs */
typedef struct {
    uint8_t committee_root[32];      // Merkle root of committee
    uint32_t committee_size;         // Number of validators
    uint64_t total_stake;           // Sum of all stakes
    basefold_raa_proof_t proof;     // Recursive proof of all VRFs
} recursive_committee_proof_t;

/* Circular chain proof - proves entire blockchain history */
typedef struct {
    blockchain_state_t current_state;    // Current chain tip
    blockchain_state_t genesis_state;    // Genesis for verification
    circular_proof_t* chain_proof;       // Circular recursive proof
    uint64_t blocks_proven;             // Number of blocks in proof
} circular_chain_proof_t;

/* Fast finality proof - accelerates consensus finality */
typedef struct {
    uint32_t start_round;               // First round in proof
    uint32_t end_round;                 // Last round in proof
    uint8_t finalized_hash[32];         // Hash of finalized block
    basefold_raa_proof_t finality_proof; // Recursive consensus proof
} fast_finality_proof_t;

/**
 * Generate recursive committee proof
 * Combines all individual VRF proofs into single recursive proof
 */
recursive_committee_proof_t* cmptr_pos_recursive_committee_prove(
    committee_t* committee,
    sha3_vrf_proof_t** vrf_proofs,  // Individual VRF proofs
    uint32_t proof_count
);

/**
 * Verify recursive committee proof
 * Verifies entire committee selection in one operation
 */
bool cmptr_pos_recursive_committee_verify(
    const recursive_committee_proof_t* proof,
    const stake_snapshot_t* snapshot,
    const uint8_t* epoch_seed
);

/**
 * Generate circular chain proof
 * Proves entire blockchain history from genesis
 */
circular_chain_proof_t* cmptr_pos_circular_chain_prove(
    pos_state_t* pos,
    const blockchain_state_t* genesis,
    uint64_t target_height
);

/**
 * Verify circular chain proof
 * Light clients can verify entire chain in 8ms
 */
bool cmptr_pos_circular_chain_verify(
    const circular_chain_proof_t* proof
);

/**
 * Generate fast finality proof
 * Accelerates finality by creating recursive proof early
 */
fast_finality_proof_t* cmptr_pos_fast_finality_prove(
    pos_state_t* pos,
    uint32_t rounds_to_prove,
    const consensus_certificate_t** certificates
);

/**
 * Parallel committee aggregation
 * Combines proofs from multiple parallel committees
 */
basefold_raa_proof_t* cmptr_pos_aggregate_parallel_committees(
    recursive_committee_proof_t** committee_proofs,
    uint32_t num_committees
);

/**
 * Cross-epoch transition proof
 * Proves correct validator set transition between epochs
 */
basefold_raa_proof_t* cmptr_pos_epoch_transition_prove(
    const stake_snapshot_t* old_snapshot,
    const stake_snapshot_t* new_snapshot,
    const validator_changes_t* changes
);

/* Performance metrics for recursive PoS */
typedef struct {
    double committee_proof_time_ms;     // Time to prove committee
    double chain_sync_time_ms;         // Time for full sync
    double finality_time_ms;           // Accelerated finality
    size_t proof_size_bytes;           // Always ~190KB
    uint64_t validators_aggregated;    // Number in recursive proof
} recursive_pos_metrics_t;

recursive_pos_metrics_t cmptr_pos_get_recursive_metrics(
    const pos_state_t* pos
);

#endif /* RECURSIVE_POS_H */