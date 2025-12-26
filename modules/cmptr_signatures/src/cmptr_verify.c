/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>

// Verify a single signature
bool cmptr_verify(cmptr_sig_system_t* system,
               const cmptr_public_key_t* public_key,
               const uint8_t* message,
               size_t message_len,
               const cmptr_signature_t* signature) {
    
    if (!system || !public_key || !message || message_len == 0 || !signature) {
        return false;
    }
    
    clock_t start = clock();
    
    // Verify message hash matches
    uint8_t computed_message_hash[CMPTR_SIG_HASH_SIZE];
    cmptr_hash_message(message, message_len, computed_message_hash);
    
    if (memcmp(computed_message_hash, signature->message_hash, CMPTR_SIG_HASH_SIZE) != 0) {
        printf("Cmptr Signatures: Message hash mismatch\n");
        return false;
    }
    
    // Verify public key hash matches
    uint8_t computed_pubkey_hash[CMPTR_SIG_HASH_SIZE];
    cmptr_hash_public_key(public_key, computed_pubkey_hash);
    
    if (memcmp(computed_pubkey_hash, signature->public_key_hash, CMPTR_SIG_HASH_SIZE) != 0) {
        printf("Cmptr Signatures: Public key hash mismatch\n");
        return false;
    }
    
    // Verify the STARK proof
    // This verifies that someone knows a private key that:
    // 1. Corresponds to the given public key
    // 2. Was used to create this signature
    
    bool valid = basefold_proof_verify(system->verifier, signature->stark_proof);
    
    clock_t end = clock();
    double elapsed_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000.0;
    
    // Update metrics
    system->metrics.total_verify_time += elapsed_ms;
    system->metrics.verify_count++;
    
    printf("Cmptr Signatures: Verified signature in %.2f ms - %s\n", 
           elapsed_ms, valid ? "VALID" : "INVALID");
    
    return valid;
}

// Verify an aggregated signature against multiple public keys and messages
bool cmptr_verify_aggregated(cmptr_sig_system_t* system,
                          const cmptr_public_key_t** public_keys,
                          const uint8_t** messages,
                          const size_t* message_lens,
                          size_t num_messages,
                          const cmptr_aggregated_signature_t* agg_signature) {
    
    if (!system || !public_keys || !messages || !message_lens || 
        num_messages == 0 || !agg_signature) {
        return false;
    }
    
    clock_t start = clock();
    
    // Verify number of signatures matches
    if (agg_signature->num_signatures != num_messages) {
        printf("Cmptr Signatures: Signature count mismatch: expected %zu, got %zu\n",
               num_messages, agg_signature->num_signatures);
        return false;
    }
    
    // Verify message hashes
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    
    for (size_t i = 0; i < num_messages; i++) {
        uint8_t message_hash[CMPTR_SIG_HASH_SIZE];
        cmptr_hash_message(messages[i], message_lens[i], message_hash);
        sha3_update(&ctx, message_hash, CMPTR_SIG_HASH_SIZE);
        
        // Verify individual message hash matches
        if (memcmp(message_hash, 
                   &agg_signature->message_hashes[i * CMPTR_SIG_HASH_SIZE], 
                   CMPTR_SIG_HASH_SIZE) != 0) {
            printf("Cmptr Signatures: Message hash mismatch at index %zu\n", i);
            return false;
        }
    }
    
    uint8_t computed_msg_hash[CMPTR_SIG_HASH_SIZE];
    sha3_final(&ctx, computed_msg_hash, 32);
    
    // Verify public key hashes
    sha3_init(&ctx, SHA3_256);
    
    for (size_t i = 0; i < num_messages; i++) {
        uint8_t pubkey_hash[CMPTR_SIG_HASH_SIZE];
        cmptr_hash_public_key(public_keys[i], pubkey_hash);
        sha3_update(&ctx, pubkey_hash, CMPTR_SIG_HASH_SIZE);
        
        // Verify individual public key hash matches
        if (memcmp(pubkey_hash,
                   &agg_signature->public_key_hashes[i * CMPTR_SIG_HASH_SIZE],
                   CMPTR_SIG_HASH_SIZE) != 0) {
            printf("Cmptr Signatures: Public key hash mismatch at index %zu\n", i);
            return false;
        }
    }
    
    uint8_t computed_pk_hash[CMPTR_SIG_HASH_SIZE];
    sha3_final(&ctx, computed_pk_hash, 32);
    
    // Verify the recursive STARK proof
    // This single proof verifies ALL signatures at once!
    bool valid = basefold_proof_verify(system->verifier, agg_signature->recursive_proof);
    
    clock_t end = clock();
    double elapsed_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000.0;
    
    // Update metrics
    system->metrics.total_verify_aggregated_time += elapsed_ms;
    system->metrics.verify_aggregated_count++;
    
    printf("Cmptr Signatures: Verified %zu aggregated signatures in %.2f ms - %s\n",
           num_messages, elapsed_ms, valid ? "VALID" : "INVALID");
    
    return valid;
}