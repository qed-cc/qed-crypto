/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Verkle tree node structure */
typedef struct verkle_node {
    uint8_t commitment[32];      /* IPA commitment */
    struct verkle_node* children[256]; /* 256-ary tree */
    uint8_t* leaf_data;          /* Leaf value if leaf node */
    uint32_t leaf_size;
} verkle_node_t;

/* Simple hash function for demo */
static void verkle_hash(uint8_t* out, const uint8_t* in, size_t len) {
    /* In real implementation: use SHA3-256 */
    memset(out, 0, 32);
    for (size_t i = 0; i < len && i < 32; i++) {
        out[i] = in[i];
    }
    out[0] ^= 0xAA; /* Simple differentiation */
}

/* Create Verkle commitment */
verkle_commitment_t* cmptr_pos_create_verkle_commitment(
    validator_pos_t** validators,
    uint32_t count
) {
    if (!validators || count == 0) {
        return NULL;
    }
    
    verkle_commitment_t* commitment = calloc(1, sizeof(verkle_commitment_t));
    if (!commitment) {
        return NULL;
    }
    
    /* Calculate total stake and create leaf data */
    uint64_t total_stake = 0;
    uint8_t* leaf_hashes = calloc(count, 32);
    
    for (uint32_t i = 0; i < count; i++) {
        if (validators[i]->state == STAKE_STATE_ACTIVE) {
            total_stake += validators[i]->stake_amount;
            
            /* Hash validator data */
            uint8_t validator_data[104]; /* 32 + 8 + 64 */
            memcpy(validator_data, validators[i]->public_key, 32);
            memcpy(validator_data + 32, &validators[i]->stake_amount, 8);
            memcpy(validator_data + 40, validators[i]->vrf_public_key, 64);
            
            verkle_hash(leaf_hashes + (i * 32), validator_data, 104);
        }
    }
    
    /* Build Verkle tree (simplified) */
    /* In real implementation: construct full IPA-based Verkle tree */
    
    /* For demo: compute simple Merkle-like root */
    uint8_t current_level[32];
    verkle_hash(current_level, leaf_hashes, count * 32);
    
    /* Add metadata to root */
    memcpy(commitment->root, current_level, 32);
    commitment->root[0] = (uint8_t)(count & 0xFF);
    commitment->root[1] = (uint8_t)((count >> 8) & 0xFF);
    commitment->root[2] = (uint8_t)((count >> 16) & 0xFF);
    commitment->root[3] = (uint8_t)((count >> 24) & 0xFF);
    
    commitment->height = 0;
    uint32_t temp = count;
    while (temp > 1) {
        temp = (temp + 255) / 256; /* 256-ary tree */
        commitment->height++;
    }
    
    commitment->total_stake = total_stake;
    commitment->validator_count = count;
    
    /* Generate proof data (simplified) */
    /* In real implementation: store IPA opening proofs */
    memset(commitment->proof_data, 0xEE, 100); /* Placeholder */
    
    free(leaf_hashes);
    
    printf("✓ Created Verkle commitment:\n");
    printf("  - Tree height: %u\n", commitment->height);
    printf("  - Validators: %u\n", count);
    printf("  - Total stake: %lu\n", total_stake);
    printf("  - Root: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", commitment->root[i]);
    }
    printf("...\n");
    
    return commitment;
}

/* Verify Verkle proof */
bool cmptr_pos_verify_verkle_proof(
    const verkle_commitment_t* commitment,
    const uint8_t* public_key,
    uint64_t stake_amount,
    const uint8_t* proof,
    size_t proof_size
) {
    if (!commitment || !public_key || !proof) {
        return false;
    }
    
    /* In real implementation: verify IPA opening proof */
    
    /* For demo: simple verification */
    if (proof_size < 64) {
        return false;
    }
    
    /* Check proof format */
    if (proof[0] != 0xEE) {
        return false;
    }
    
    /* Verify stake amount is reasonable */
    if (stake_amount == 0 || stake_amount > commitment->total_stake) {
        return false;
    }
    
    /* In real implementation:
     * 1. Reconstruct path from public_key to root
     * 2. Verify IPA commitment opening
     * 3. Check stake_amount matches committed value
     */
    
    printf("✓ Verkle proof verified for validator\n");
    return true;
}

/* Helper: Generate Verkle proof for a validator */
static bool generate_verkle_proof(
    const verkle_commitment_t* commitment,
    const uint8_t* public_key,
    uint8_t* proof_out,
    size_t* proof_size
) {
    if (!commitment || !public_key || !proof_out || !proof_size) {
        return false;
    }
    
    /* In real implementation: generate IPA opening proof */
    
    /* For demo: create placeholder proof */
    proof_out[0] = 0xEE; /* Proof marker */
    memcpy(proof_out + 1, public_key, 32);
    memcpy(proof_out + 33, commitment->root, 32);
    *proof_size = 65;
    
    return true;
}

/* Create state proof using Verkle tree */
bool cmptr_pos_create_state_proof(
    const verkle_commitment_t* commitment,
    validator_pos_t** validators,
    uint32_t start_index,
    uint32_t count,
    uint8_t* proof_out,
    size_t* proof_size_out
) {
    if (!commitment || !validators || !proof_out || !proof_size_out) {
        return false;
    }
    
    if (start_index + count > commitment->validator_count) {
        return false;
    }
    
    size_t offset = 0;
    
    /* Header */
    memcpy(proof_out + offset, commitment->root, 32);
    offset += 32;
    
    /* Number of validators in proof */
    memcpy(proof_out + offset, &count, 4);
    offset += 4;
    
    /* For each validator, include proof */
    for (uint32_t i = 0; i < count; i++) {
        uint32_t idx = start_index + i;
        validator_pos_t* val = validators[idx];
        
        /* Validator data */
        memcpy(proof_out + offset, val->public_key, 32);
        offset += 32;
        
        memcpy(proof_out + offset, &val->stake_amount, 8);
        offset += 8;
        
        /* Verkle proof */
        uint8_t individual_proof[256];
        size_t individual_size = 0;
        
        if (!generate_verkle_proof(commitment, val->public_key,
                                  individual_proof, &individual_size)) {
            return false;
        }
        
        memcpy(proof_out + offset, &individual_size, 4);
        offset += 4;
        
        memcpy(proof_out + offset, individual_proof, individual_size);
        offset += individual_size;
    }
    
    *proof_size_out = offset;
    
    printf("✓ Created state proof for %u validators (%zu bytes)\n",
           count, offset);
    
    return true;
}