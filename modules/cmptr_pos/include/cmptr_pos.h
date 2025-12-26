/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_H
#define CMPTR_POS_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include "cmptr_accumulator.h"
#include "cmptr_blockchain.h"
#include "basefold_raa.h"
#include "cmptr_pos_types.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct pos_state pos_state_t;
typedef struct committee committee_t;
typedef struct narwhal_dag narwhal_dag_t;
typedef struct mysticeti_state mysticeti_state_t;
typedef struct consensus_certificate consensus_certificate_t;

/* Type alias for stake snapshot */
typedef struct verkle_commitment stake_snapshot_t;

/* Verkle commitment for stake snapshots */
typedef struct verkle_commitment {
    uint8_t root[32];              /* Verkle tree root */
    uint32_t height;               /* Tree height */
    uint64_t total_stake;          /* Sum of all stakes */
    uint32_t validator_count;      /* Number of validators */
    uint8_t proof_data[8192];      /* Compressed proof data */
} verkle_commitment_t;

/* Lattice-based VRF output */
typedef struct {
    uint8_t output[64];            /* VRF output (512 bits) */
    uint8_t proof[16384];          /* Lattice proof */
    uint32_t proof_size;           /* Actual proof size */
    bool is_valid;                 /* Verification result */
} lattice_vrf_t;

/* Committee for an epoch */
struct committee {
    uint32_t epoch;                /* Epoch number */
    validator_pos_t** members;     /* Committee members */
    uint32_t size;                 /* Committee size */
    uint32_t threshold;            /* Byzantine threshold */
    uint8_t seed[32];              /* Random seed from VRF */
};

/* Narwhal DAG vertex */
typedef struct {
    uint8_t id[32];                /* Vertex hash */
    uint32_t round;                /* DAG round */
    uint8_t author[32];            /* Creator's public key */
    uint8_t parent_hashes[4][32];  /* Parent vertices */
    uint32_t parent_count;
    
    /* Blob data */
    uint8_t* blob_data;            /* Transaction data */
    uint32_t blob_size;
    uint8_t blob_hash[32];         /* SHA3-256 of blob */
    
    /* Signatures */
    uint8_t signature[64];         /* Author's signature */
    uint64_t timestamp;
} narwhal_vertex_t;

/* Narwhal DAG state */
struct narwhal_dag {
    narwhal_vertex_t** vertices;   /* All vertices */
    uint32_t vertex_count;
    uint32_t current_round;
    
    /* Round tracking */
    uint32_t* round_sizes;         /* Vertices per round */
    uint32_t max_rounds;
    
    /* Synchronization */
    pthread_rwlock_t dag_lock;
};

/* Mysticeti ordering state */
struct mysticeti_state {
    narwhal_dag_t* dag;            /* Input DAG */
    
    /* Ordered output */
    narwhal_vertex_t** ordered_vertices;
    uint32_t ordered_count;
    
    /* Consensus tracking */
    uint32_t* vertex_votes;        /* Vote count per vertex */
    bool* vertex_decided;          /* Decision status */
    
    /* Byzantine fault tolerance */
    uint32_t honest_stake;         /* Honest validator stake */
    uint32_t total_stake;          /* Total stake */
};

/* Consensus certificate (STARK proof) */
struct consensus_certificate {
    /* Certificate metadata */
    uint32_t epoch;
    uint64_t block_height;
    uint8_t block_hash[32];
    
    /* Recursive STARK proof */
    uint8_t stark_proof[190*1024]; /* ~190KB proof */
    uint32_t proof_size;
    
    /* Certificate covers */
    verkle_commitment_t stake_snapshot;
    uint8_t committee_root[32];    /* Merkle root of committee */
    uint8_t dag_root[32];          /* Commitment to DAG */
    uint8_t ordering_root[32];     /* Commitment to ordering */
    
    /* Signature aggregation */
    uint8_t aggregate_signature[96]; /* BLS aggregate (if needed) */
    uint64_t signing_stake;        /* Stake that signed */
};

/* Main PoS state */
struct pos_state {
    /* Configuration */
    uint32_t epoch_length;         /* Blocks per epoch */
    uint32_t committee_size;       /* Target committee size */
    uint64_t min_stake;            /* Minimum stake amount */
    uint32_t unbonding_period;     /* Epochs to unbond */
    
    /* Current state */
    uint32_t current_epoch;
    uint64_t current_slot;
    consensus_phase_t phase;
    
    /* Validators */
    validator_pos_t** validators;
    uint32_t validator_count;
    uint64_t total_staked;
    
    /* Current consensus */
    committee_t* current_committee;
    narwhal_dag_t* current_dag;
    mysticeti_state_t* ordering_state;
    
    /* Blockchain integration */
    cmptr_accumulator_t* accumulator;
    blockchain_t* blockchain;
    
    /* Synchronization */
    pthread_mutex_t state_mutex;
    pthread_t consensus_thread;
    bool is_running;
};

/* Initialize PoS system */
pos_state_t* cmptr_pos_init(
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain
);

void cmptr_pos_destroy(pos_state_t* pos);

/* Validator management */
bool cmptr_pos_add_validator(
    pos_state_t* pos,
    const uint8_t* public_key,
    uint64_t stake_amount,
    const uint8_t* vrf_public_key
);

bool cmptr_pos_remove_validator(
    pos_state_t* pos,
    const uint8_t* public_key
);

bool cmptr_pos_update_stake(
    pos_state_t* pos,
    const uint8_t* public_key,
    uint64_t new_stake
);

/* Consensus operations */
bool cmptr_pos_start_consensus(pos_state_t* pos);
bool cmptr_pos_stop_consensus(pos_state_t* pos);

/* Epoch management */
bool cmptr_pos_advance_epoch(pos_state_t* pos);
stake_snapshot_t* cmptr_pos_take_snapshot(pos_state_t* pos);
committee_t* cmptr_pos_select_committee(
    pos_state_t* pos,
    const stake_snapshot_t* snapshot
);

/* DAG construction */
narwhal_dag_t* cmptr_pos_create_dag(void);
bool cmptr_pos_add_vertex(
    narwhal_dag_t* dag,
    const narwhal_vertex_t* vertex
);
bool cmptr_pos_simulate_dag_round(
    narwhal_dag_t* dag,
    committee_t* committee,
    uint32_t transactions_per_validator
);
void cmptr_pos_destroy_dag(narwhal_dag_t* dag);

/* Mysticeti ordering */
mysticeti_state_t* cmptr_pos_create_ordering(
    narwhal_dag_t* dag,
    committee_t* committee
);

bool cmptr_pos_run_ordering(
    mysticeti_state_t* ordering
);

uint32_t cmptr_pos_extract_ordered_transactions(
    mysticeti_state_t* ordering,
    transaction_t** transactions_out,
    uint32_t max_transactions
);

void cmptr_pos_destroy_ordering(mysticeti_state_t* ordering);

/* STARK certificate generation */
consensus_certificate_t* cmptr_pos_generate_certificate(
    pos_state_t* pos,
    const stake_snapshot_t* snapshot,
    const committee_t* committee,
    const mysticeti_state_t* ordering
);

bool cmptr_pos_verify_certificate(
    const consensus_certificate_t* cert
);

/* Block production */
block_t* cmptr_pos_produce_block(
    pos_state_t* pos,
    const consensus_certificate_t* cert,
    transaction_t** transactions,
    uint32_t tx_count
);

/* Lattice VRF operations */
bool cmptr_pos_generate_vrf_keys(
    uint8_t* public_key_out,
    uint8_t* private_key_out
);

lattice_vrf_t* cmptr_pos_compute_vrf(
    const uint8_t* private_key,
    const uint8_t* message,
    size_t message_len
);

bool cmptr_pos_verify_vrf(
    const uint8_t* public_key,
    const uint8_t* message,
    size_t message_len,
    const lattice_vrf_t* vrf_output
);

/* Verkle tree operations */
verkle_commitment_t* cmptr_pos_create_verkle_commitment(
    validator_pos_t** validators,
    uint32_t count
);

bool cmptr_pos_verify_verkle_proof(
    const verkle_commitment_t* commitment,
    const uint8_t* public_key,
    uint64_t stake_amount,
    const uint8_t* proof,
    size_t proof_size
);

/* Metrics and monitoring */
typedef struct {
    uint32_t current_epoch;
    uint64_t current_slot;
    uint32_t validator_count;
    uint64_t total_staked;
    uint32_t committee_size;
    double finality_time_ms;
    uint64_t certificates_generated;
    uint64_t dag_vertices;
    double ordering_latency_ms;
} pos_metrics_t;

pos_metrics_t cmptr_pos_get_metrics(const pos_state_t* pos);

/* Slashing conditions */
bool cmptr_pos_report_equivocation(
    pos_state_t* pos,
    const uint8_t* validator_key,
    const uint8_t* evidence,
    size_t evidence_size
);

bool cmptr_pos_report_invalid_block(
    pos_state_t* pos,
    const uint8_t* validator_key,
    const block_t* invalid_block
);

/* Committee management */
void cmptr_pos_free_committee(committee_t* committee);

/* Consensus round */
bool cmptr_pos_run_consensus_round(
    pos_state_t* pos,
    transaction_t** pending_transactions,
    uint32_t tx_count
);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_POS_H */