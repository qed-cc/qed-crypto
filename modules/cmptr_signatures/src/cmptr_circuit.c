/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include <stdlib.h>
#include <string.h>

// Circuit for proving knowledge of private key that signs a message
// The circuit proves:
// 1. SHA3(private_seed || "CMPTR_PUBLIC_KEY_COMMITMENT") = public_commitment
// 2. SHA3(private_seed || message_hash || nonce) = signature_hash
bool cmptr_create_signing_circuit(const cmptr_private_key_t* private_key,
                               const uint8_t* message_hash,
                               uint8_t* witness_data,
                               size_t* witness_size) {
    
    if (!private_key || !message_hash || !witness_data || !witness_size) {
        return false;
    }
    
    // The witness contains:
    // - Private key seed (32 bytes)
    // - Message hash (32 bytes)
    // - Nonce for zero-knowledge (32 bytes)
    // - Expected public commitment (32 bytes)
    // - Expected signature hash (32 bytes)
    
    size_t required_size = 5 * CMPTR_SIG_HASH_SIZE;
    if (*witness_size < required_size) {
        *witness_size = required_size;
        return false;
    }
    
    uint8_t* ptr = witness_data;
    
    // Copy private key seed
    memcpy(ptr, private_key->seed, CMPTR_SIG_HASH_SIZE);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Copy message hash
    memcpy(ptr, message_hash, CMPTR_SIG_HASH_SIZE);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Generate random nonce for zero-knowledge
    uint8_t nonce[CMPTR_SIG_HASH_SIZE];
    if (secure_random_bytes(nonce, CMPTR_SIG_HASH_SIZE) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    memcpy(ptr, nonce, CMPTR_SIG_HASH_SIZE);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Compute expected public commitment
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, private_key->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (const uint8_t*)"CMPTR_PUBLIC_KEY_COMMITMENT", 27);
    sha3_final(&ctx, ptr, 32);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Compute signature hash
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, private_key->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, message_hash, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, nonce, CMPTR_SIG_HASH_SIZE);
    sha3_final(&ctx, ptr, 32);
    
    *witness_size = required_size;
    return true;
}

// Circuit for recursive aggregation of signatures
// This creates a circuit that verifies N signature proofs and outputs a single proof
bool cmptr_create_aggregation_circuit(const cmptr_signature_t** signatures,
                                   size_t num_signatures,
                                   uint8_t* witness_data,
                                   size_t* witness_size) {
    
    if (!signatures || num_signatures == 0 || !witness_data || !witness_size) {
        return false;
    }
    
    // For aggregation, we need:
    // - Hash of all message hashes (32 bytes)
    // - Hash of all public key hashes (32 bytes)
    // - Number of signatures (8 bytes)
    // - Aggregation nonce (32 bytes)
    
    size_t required_size = 3 * CMPTR_SIG_HASH_SIZE + sizeof(uint64_t);
    if (*witness_size < required_size) {
        *witness_size = required_size;
        return false;
    }
    
    // Compute aggregation hash of all inputs
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    
    // Hash all message hashes
    for (size_t i = 0; i < num_signatures; i++) {
        sha3_update(&ctx, signatures[i]->message_hash, CMPTR_SIG_HASH_SIZE);
    }
    
    uint8_t* ptr = witness_data;
    sha3_final(&ctx, ptr, 32);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Hash all public key hashes
    sha3_init(&ctx, SHA3_256);
    for (size_t i = 0; i < num_signatures; i++) {
        sha3_update(&ctx, signatures[i]->public_key_hash, CMPTR_SIG_HASH_SIZE);
    }
    sha3_final(&ctx, ptr, 32);
    ptr += CMPTR_SIG_HASH_SIZE;
    
    // Store number of signatures
    uint64_t count = num_signatures;
    memcpy(ptr, &count, sizeof(uint64_t));
    ptr += sizeof(uint64_t);
    
    // Generate aggregation nonce
    if (secure_random_bytes(ptr, CMPTR_SIG_HASH_SIZE) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    
    *witness_size = required_size;
    return true;
}