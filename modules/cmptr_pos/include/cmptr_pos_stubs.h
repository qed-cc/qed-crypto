/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_STUBS_H
#define CMPTR_POS_STUBS_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

/* Stub for cmptr_pos_compute_vrf - would be in cmptr_pos.h */
typedef struct {
    uint8_t output[32];
    uint8_t proof[128];
} vrf_output_t;

static inline vrf_output_t* cmptr_pos_compute_vrf(
    const uint8_t* private_key,
    const uint8_t* seed,
    size_t seed_len
) {
    /* Stub implementation */
    vrf_output_t* vrf = calloc(1, sizeof(vrf_output_t));
    if (vrf && private_key && seed) {
        /* Generate pseudo-random output */
        for (size_t i = 0; i < 32; i++) {
            vrf->output[i] = (uint8_t)(seed[i % seed_len] ^ private_key[i % 32]);
        }
    }
    return vrf;
}

/* Stub for cmptr_accumulator functions */
typedef struct cmptr_accumulator cmptr_accumulator_t;

static inline cmptr_accumulator_t* cmptr_accumulator_init(void) {
    return (cmptr_accumulator_t*)calloc(1, 1024); /* Stub */
}

static inline void cmptr_accumulator_destroy(cmptr_accumulator_t* acc) {
    free(acc);
}

/* Stub for cmptr_blockchain functions */
static inline blockchain_t* cmptr_blockchain_init(void) {
    return (blockchain_t*)calloc(1, 1024); /* Stub */
}

static inline void cmptr_blockchain_destroy(blockchain_t* bc) {
    free(bc);
}

/* Stub for cmptr_pos functions */
typedef struct {
    uint32_t validator_count;
    uint64_t* validator_stakes;
    uint8_t vrf_private_key[32];
    uint8_t epoch_seed[32];
} pos_state_t;

static inline pos_state_t* cmptr_pos_init(
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain
) {
    (void)accumulator;
    (void)blockchain;
    
    pos_state_t* state = calloc(1, sizeof(pos_state_t));
    if (state) {
        state->validator_count = 100;
        state->validator_stakes = calloc(state->validator_count, sizeof(uint64_t));
        for (uint32_t i = 0; i < state->validator_count; i++) {
            state->validator_stakes[i] = 1000000; /* 1M tokens each */
        }
    }
    return state;
}

static inline void cmptr_pos_destroy(pos_state_t* state) {
    if (state) {
        free(state->validator_stakes);
        free(state);
    }
}

#endif /* CMPTR_POS_STUBS_H */