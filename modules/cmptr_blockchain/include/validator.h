/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_VALIDATOR_H
#define CMPTR_VALIDATOR_H

#include "cmptr_blockchain.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Validator-specific functions */
bool validator_validate_block(
    node_t* node,
    const block_t* block
);

bool validator_sync(node_t* node);

bool validator_fast_sync(
    node_t* validator_node,
    const uint8_t* accumulator_proof,
    size_t proof_size,
    uint64_t proof_height
);

bool validator_get_state_proof(
    const node_t* node,
    uint8_t* proof_out,
    size_t* proof_size
);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_VALIDATOR_H */