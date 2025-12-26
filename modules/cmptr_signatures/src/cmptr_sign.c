/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>

// Sign a message with a STARK proof
cmptr_signature_t* cmptr_sign(cmptr_sig_system_t* system,
                         const cmptr_private_key_t* private_key,
                         const uint8_t* message,
                         size_t message_len) {
    
    if (!system || !private_key || !message || message_len == 0) {
        return NULL;
    }
    
    clock_t start = clock();
    
    // Allocate signature structure
    cmptr_signature_t* sig = calloc(1, sizeof(cmptr_signature_t));
    if (!sig) {
        return NULL;
    }
    
    // Hash the message
    cmptr_hash_message(message, message_len, sig->message_hash);
    
    // Compute public key from private key and hash it
    cmptr_public_key_t temp_pubkey;
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, private_key->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (const uint8_t*)"CMPTR_PUBLIC_KEY_COMMITMENT", 27);
    sha3_final(&ctx, temp_pubkey.commitment, 32);
    
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, private_key->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, private_key->chain_code, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (const uint8_t*)"CMPTR_VERIFICATION_KEY", 22);
    sha3_final(&ctx, temp_pubkey.verification_key, 32);
    
    cmptr_hash_public_key(&temp_pubkey, sig->public_key_hash);
    
    // Generate nonce for zero-knowledge
    if (secure_random_bytes(sig->nonce, CMPTR_SIG_HASH_SIZE) != SECURE_RANDOM_SUCCESS) {
        free(sig);
        return NULL;
    }
    
    // Set timestamp
    sig->timestamp = (uint64_t)time(NULL);
    
    // Create witness data for the signing circuit
    uint8_t witness_data[1024];
    size_t witness_size = sizeof(witness_data);
    
    if (!cmptr_create_signing_circuit(private_key, sig->message_hash, 
                                   witness_data, &witness_size)) {
        free(sig);
        return NULL;
    }
    
    // Create the STARK proof
    // The circuit proves knowledge of private key that:
    // 1. Corresponds to the public key
    // 2. Was used to sign the message
    
    // For now, we'll create a placeholder proof
    // In real implementation, this would generate a proper STARK proof
    sig->stark_proof = basefold_proof_placeholder_create(system->config);
    if (!sig->stark_proof) {
        free(sig);
        return NULL;
    }
    
    clock_t end = clock();
    double elapsed_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000.0;
    
    // Update metrics
    system->metrics.total_sign_time += elapsed_ms;
    system->metrics.sign_count++;
    
    printf("Cmptr Signatures: Signed message in %.2f ms\n", elapsed_ms);
    
    return sig;
}