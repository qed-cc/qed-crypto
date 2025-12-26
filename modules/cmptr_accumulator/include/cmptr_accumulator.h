/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_ACCUMULATOR_H
#define CMPTR_ACCUMULATOR_H

#include <stdint.h>
#include <stdbool.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct cmptr_accumulator cmptr_accumulator_t;
typedef struct nullifier_set nullifier_set_t;
typedef struct kernel_set kernel_set_t;

/* Token states */
typedef enum {
    TOKEN_PARKED = 0,    /* Permanent, cannot be spent */
    TOKEN_ACTIVE = 1     /* Spendable for 1 year */
} token_state_t;

/* Token structure */
typedef struct {
    uint8_t commitment[32];      /* Hidden token data */
    uint8_t nullifier[32];       /* Spend authorization */
    token_state_t state;         /* PARKED or ACTIVE */
    uint64_t activation_time;    /* When moved to ACTIVE */
    uint64_t expiry_time;        /* activation_time + 1 year */
    uint8_t owner_pubkey[32];    /* Owner's public key */
} token_t;

/* Proof of Work structure */
typedef struct {
    uint8_t challenge[32];       /* SHA3 of previous block + target */
    uint8_t nonce[32];           /* Miner's nonce */
    uint8_t solution_hash[32];   /* SHA3(challenge || nonce) */
    uint32_t difficulty;         /* Number of leading zeros required */
    uint64_t timestamp;          /* When solution found */
} proof_of_work_t;

/* Proof types */
typedef struct {
    uint8_t proof_data[190*1024];    /* BaseFold RAA recursive proof */
    uint32_t proof_size;
    proof_of_work_t pow;             /* Required PoW for this operation */
} accumulator_proof_t;

/* Transaction types */
typedef struct {
    accumulator_proof_t ownership_proof;
    uint8_t new_nullifier[32];
    uint64_t activation_time;
    uint8_t active_commitment[32];
    proof_of_work_t pow;             /* PoW to activate token */
} activation_tx_t;

typedef struct {
    accumulator_proof_t active_proof;
    accumulator_proof_t unspent_proof;
    uint8_t nullifier[32];
    uint8_t output_commitment[32];
    proof_of_work_t pow;             /* PoW to spend token */
} spend_tx_t;

/* Accumulator statistics */
typedef struct {
    uint64_t total_tokens;           /* Total tokens ever created */
    uint64_t parked_tokens;          /* Currently parked */
    uint64_t active_tokens;          /* Currently active */
    uint64_t nullifier_count;        /* Current nullifier set size */
    uint64_t pruned_count;           /* Total pruned nullifiers */
    uint32_t current_difficulty;     /* Current PoW difficulty */
    double hash_rate;                /* Network hash rate */
} accumulator_stats_t;

/* Main accumulator structure */
struct cmptr_accumulator {
    /* Core accumulators */
    uint8_t nullifier_proof[190*1024];   /* Recursive proof of nullifiers */
    uint8_t kernel_proof[190*1024];      /* Recursive proof of kernels */
    uint8_t pruning_proof[190*1024];     /* Proof of correct pruning */
    
    /* Recent data caches */
    nullifier_set_t* recent_nullifiers;   /* Last 365 days */
    kernel_set_t* recent_kernels;         /* For fast queries */
    
    /* Proof of Work */
    uint32_t pow_difficulty;              /* Current difficulty */
    uint64_t pow_target_time;             /* Target time between blocks (ms) */
    uint8_t pow_challenge[32];            /* Current PoW challenge */
    
    /* Statistics */
    accumulator_stats_t stats;
};

/* Initialization and cleanup */
cmptr_accumulator_t* cmptr_accumulator_init(void);
void cmptr_accumulator_destroy(cmptr_accumulator_t* acc);

/* Token operations */
token_t cmptr_accumulator_mint_token(
    cmptr_accumulator_t* acc,
    const uint8_t owner_pubkey[32],
    proof_of_work_t* pow
);

activation_tx_t cmptr_accumulator_activate_token(
    cmptr_accumulator_t* acc,
    const token_t* token,
    const uint8_t secret[32],
    proof_of_work_t* pow
);

spend_tx_t cmptr_accumulator_spend_token(
    cmptr_accumulator_t* acc,
    const token_t* token,
    const uint8_t recipient_pubkey[32],
    const uint8_t secret[32],
    proof_of_work_t* pow
);

/* Proof of Work functions */
bool cmptr_accumulator_verify_pow(
    const proof_of_work_t* pow,
    uint32_t required_difficulty
);

proof_of_work_t cmptr_accumulator_mine_pow(
    const uint8_t challenge[32],
    uint32_t difficulty
);

void cmptr_accumulator_adjust_difficulty(
    cmptr_accumulator_t* acc,
    uint64_t actual_time,
    uint64_t target_time
);

/* Verification */
bool cmptr_accumulator_verify_proof(
    const cmptr_accumulator_t* acc,
    const accumulator_proof_t* proof
);

bool cmptr_accumulator_verify_activation(
    const cmptr_accumulator_t* acc,
    const activation_tx_t* tx
);

bool cmptr_accumulator_verify_spend(
    const cmptr_accumulator_t* acc,
    const spend_tx_t* tx
);

/* Pruning operations */
uint64_t cmptr_accumulator_prune_expired(cmptr_accumulator_t* acc);
bool cmptr_accumulator_needs_pruning(const cmptr_accumulator_t* acc);

/* Query operations */
bool cmptr_accumulator_is_nullifier_spent(
    const cmptr_accumulator_t* acc,
    const uint8_t nullifier[32]
);

bool cmptr_accumulator_token_exists(
    const cmptr_accumulator_t* acc,
    const uint8_t commitment[32]
);

/* Statistics */
accumulator_stats_t cmptr_accumulator_get_stats(const cmptr_accumulator_t* acc);

/* Serialization */
size_t cmptr_accumulator_serialize(
    const cmptr_accumulator_t* acc,
    uint8_t* buffer,
    size_t buffer_size
);

cmptr_accumulator_t* cmptr_accumulator_deserialize(
    const uint8_t* buffer,
    size_t buffer_size
);

/* High-TPS aggregation layer */
typedef struct aggregator aggregator_t;
typedef struct proof_generator proof_generator_t;
typedef struct block_producer block_producer_t;

/* Aggregator functions (Layer 1: 1000 TPS each) */
aggregator_t* cmptr_accumulator_create_aggregator(
    cmptr_accumulator_t* acc,
    uint32_t aggregator_id
);

void cmptr_accumulator_submit_to_aggregator(
    aggregator_t* agg,
    const spend_tx_t* tx
);

/* Proof generator functions (Layer 2: 10K TPS each) */
proof_generator_t* cmptr_accumulator_create_generator(
    cmptr_accumulator_t* acc,
    aggregator_t* aggregators[],
    size_t num_aggregators
);

/* Block producer functions (Layer 3: 100K TPS each) */
block_producer_t* cmptr_accumulator_create_producer(
    cmptr_accumulator_t* acc,
    proof_generator_t* generators[],
    size_t num_generators
);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_ACCUMULATOR_H */