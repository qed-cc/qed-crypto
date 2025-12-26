/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_exchange.h"
#include "../../sha3/include/sha3.h"
#include "../../common/include/secure_random.h"
#include <stdlib.h>
#include <string.h>

// Exchange system state
struct cmptr_exchange_system {
    // In full implementation, this would contain:
    // - BaseFold RAA prover/verifier
    // - Circuit for key exchange
    // - Domain parameters
    uint32_t dummy_field;
};

// Private key: just random bytes for now
struct cmptr_exchange_private {
    uint8_t key[CMPTR_EXCHANGE_PRIVATE_SIZE];
};

// Public key: in full implementation, this would be a STARK proof
// For now, we simulate with SHA3 of private key + padding
struct cmptr_exchange_public {
    uint8_t data[CMPTR_EXCHANGE_PUBLIC_SIZE];
    size_t actual_size;
};

// Transcript for authenticated key exchange
struct cmptr_exchange_transcript {
    sha3_ctx ctx;
    bool finalized;
};

// Initialize exchange system
cmptr_exchange_system_t* cmptr_exchange_init(void) {
    cmptr_exchange_system_t* system = calloc(1, sizeof(cmptr_exchange_system_t));
    if (!system) return NULL;
    
    // In full implementation:
    // - Initialize BaseFold RAA prover/verifier
    // - Set up exchange circuit
    // - Configure domain parameters
    
    return system;
}

// Generate ephemeral key pair
bool cmptr_exchange_keygen(
    cmptr_exchange_system_t* system,
    cmptr_exchange_private_t** private_key,
    cmptr_exchange_public_t** public_key
) {
    if (!system || !private_key || !public_key) return false;
    
    // Generate private key
    *private_key = calloc(1, sizeof(cmptr_exchange_private_t));
    if (!*private_key) return false;
    
    if (secure_random_bytes((*private_key)->key, CMPTR_EXCHANGE_PRIVATE_SIZE) != SECURE_RANDOM_SUCCESS) {
        free(*private_key);
        *private_key = NULL;
        return false;
    }
    
    // Generate public key (simulated STARK proof)
    *public_key = calloc(1, sizeof(cmptr_exchange_public_t));
    if (!*public_key) {
        free(*private_key);
        *private_key = NULL;
        return false;
    }
    
    // In full implementation:
    // 1. Create witness from private key
    // 2. Generate STARK proof of knowledge
    // 3. Proof shows: "I know x such that commitment = SHA3(x)"
    
    // For now, simulate with hash + padding
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"public_key_v1", 13);
    sha3_update(&ctx, (*private_key)->key, CMPTR_EXCHANGE_PRIVATE_SIZE);
    sha3_final(&ctx, (*public_key)->data, 32);
    
    // Pad to simulate STARK proof size
    memset((*public_key)->data + 32, 0xAA, 1000);  // Some pattern
    (*public_key)->actual_size = 1032;  // Much smaller than real STARK
    
    return true;
}

// Create commitment to public key
bool cmptr_exchange_commit(
    const cmptr_exchange_public_t* public_key,
    uint8_t commitment_out[CMPTR_EXCHANGE_COMMIT_SIZE]
) {
    if (!public_key || !commitment_out) return false;
    
    // Commitment = SHA3(public_key_data)
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, public_key->data, public_key->actual_size);
    sha3_final(&ctx, commitment_out, 32);
    
    return true;
}

// Reveal public key (STARK proof)
bool cmptr_exchange_reveal(
    const cmptr_exchange_public_t* public_key,
    uint8_t* proof_out,
    size_t* proof_len
) {
    if (!public_key || !proof_out || !proof_len) return false;
    
    // Copy the proof data
    memcpy(proof_out, public_key->data, public_key->actual_size);
    *proof_len = public_key->actual_size;
    
    return true;
}

// Derive shared secret
bool cmptr_exchange_derive(
    cmptr_exchange_system_t* system,
    const cmptr_exchange_private_t* private_key,
    const uint8_t* peer_proof,
    size_t peer_proof_len,
    uint8_t shared_secret_out[CMPTR_EXCHANGE_SHARED_SIZE]
) {
    if (!system || !private_key || !peer_proof || !shared_secret_out) return false;
    
    // In full implementation:
    // 1. Verify peer's STARK proof
    // 2. Extract peer's commitment from proof
    // 3. Compute shared secret using circuit evaluation
    
    // For now, simulate with SHA3 of both keys
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"shared_secret_v1", 16);
    sha3_update(&ctx, private_key->key, CMPTR_EXCHANGE_PRIVATE_SIZE);
    sha3_update(&ctx, peer_proof, peer_proof_len);
    sha3_final(&ctx, shared_secret_out, 32);
    
    return true;
}

// Verify commitment matches revealed key
bool cmptr_exchange_verify_commitment(
    const uint8_t commitment[CMPTR_EXCHANGE_COMMIT_SIZE],
    const uint8_t* proof,
    size_t proof_len
) {
    if (!commitment || !proof) return false;
    
    // Recompute commitment
    uint8_t computed[CMPTR_EXCHANGE_COMMIT_SIZE];
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, proof, proof_len);
    sha3_final(&ctx, computed, 32);
    
    // Constant-time comparison
    return cmptr_exchange_ct_equal(commitment, computed, CMPTR_EXCHANGE_COMMIT_SIZE);
}

// Create transcript
cmptr_exchange_transcript_t* cmptr_exchange_transcript_new(void) {
    cmptr_exchange_transcript_t* transcript = calloc(1, sizeof(cmptr_exchange_transcript_t));
    if (!transcript) return NULL;
    
    sha3_init(&transcript->ctx, SHA3_256);
    sha3_update(&transcript->ctx, (const uint8_t*)"cmptr_exchange_v1", 17);
    transcript->finalized = false;
    
    return transcript;
}

// Add to transcript
void cmptr_exchange_transcript_add(
    cmptr_exchange_transcript_t* transcript,
    const char* label,
    const uint8_t* data,
    size_t len
) {
    if (!transcript || transcript->finalized) return;
    
    // Add label length + label + data length + data
    uint32_t label_len = strlen(label);
    sha3_update(&transcript->ctx, (const uint8_t*)&label_len, 4);
    sha3_update(&transcript->ctx, (const uint8_t*)label, label_len);
    sha3_update(&transcript->ctx, (const uint8_t*)&len, sizeof(len));
    sha3_update(&transcript->ctx, data, len);
}

// Finalize transcript
bool cmptr_exchange_transcript_finalize(
    cmptr_exchange_transcript_t* transcript,
    const uint8_t shared_secret[CMPTR_EXCHANGE_SHARED_SIZE],
    uint8_t context_out[32]
) {
    if (!transcript || transcript->finalized || !shared_secret || !context_out) {
        return false;
    }
    
    // Add shared secret to transcript
    sha3_update(&transcript->ctx, shared_secret, CMPTR_EXCHANGE_SHARED_SIZE);
    
    // Finalize
    sha3_final(&transcript->ctx, context_out, 32);
    transcript->finalized = true;
    
    return true;
}

// Export private key
bool cmptr_exchange_private_export(
    const cmptr_exchange_private_t* private_key,
    uint8_t out[CMPTR_EXCHANGE_PRIVATE_SIZE]
) {
    if (!private_key || !out) return false;
    memcpy(out, private_key->key, CMPTR_EXCHANGE_PRIVATE_SIZE);
    return true;
}

// Import private key
cmptr_exchange_private_t* cmptr_exchange_private_import(
    cmptr_exchange_system_t* system,
    const uint8_t data[CMPTR_EXCHANGE_PRIVATE_SIZE]
) {
    if (!system || !data) return NULL;
    
    cmptr_exchange_private_t* private_key = calloc(1, sizeof(cmptr_exchange_private_t));
    if (!private_key) return NULL;
    
    memcpy(private_key->key, data, CMPTR_EXCHANGE_PRIVATE_SIZE);
    return private_key;
}

// Free resources
void cmptr_exchange_system_free(cmptr_exchange_system_t* system) {
    if (!system) return;
    free(system);
}

void cmptr_exchange_private_free(cmptr_exchange_private_t* private_key) {
    if (!private_key) return;
    memset(private_key->key, 0, sizeof(private_key->key));
    free(private_key);
}

void cmptr_exchange_public_free(cmptr_exchange_public_t* public_key) {
    if (!public_key) return;
    memset(public_key->data, 0, sizeof(public_key->data));
    free(public_key);
}

void cmptr_exchange_transcript_free(cmptr_exchange_transcript_t* transcript) {
    if (!transcript) return;
    memset(transcript, 0, sizeof(*transcript));
    free(transcript);
}

// Constant-time comparison
bool cmptr_exchange_ct_equal(const uint8_t* a, const uint8_t* b, size_t len) {
    uint8_t diff = 0;
    for (size_t i = 0; i < len; i++) {
        diff |= a[i] ^ b[i];
    }
    return diff == 0;
}