/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include "secure_random.h"
#include <stdlib.h>
#include <string.h>

// Generate a new Cmptr Signatures key pair
bool cmptr_keygen(cmptr_sig_system_t* system, 
                cmptr_private_key_t** private_key,
                cmptr_public_key_t** public_key) {
    
    if (!system || !private_key || !public_key) {
        return false;
    }
    
    // Allocate key structures
    *private_key = calloc(1, sizeof(cmptr_private_key_t));
    *public_key = calloc(1, sizeof(cmptr_public_key_t));
    
    if (!*private_key || !*public_key) {
        free(*private_key);
        free(*public_key);
        *private_key = NULL;
        *public_key = NULL;
        return false;
    }
    
    // Generate random seed for private key
    if (secure_random_bytes((*private_key)->seed, CMPTR_SIG_HASH_SIZE) != SECURE_RANDOM_SUCCESS) {
        cmptr_private_key_free(*private_key);
        cmptr_public_key_free(*public_key);
        *private_key = NULL;
        *public_key = NULL;
        return false;
    }
    
    // Generate chain code for deterministic derivation
    if (secure_random_bytes((*private_key)->chain_code, CMPTR_SIG_HASH_SIZE) != SECURE_RANDOM_SUCCESS) {
        cmptr_private_key_free(*private_key);
        cmptr_public_key_free(*public_key);
        *private_key = NULL;
        *public_key = NULL;
        return false;
    }
    
    // Derive public key commitment using SHA3-256
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (*private_key)->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (const uint8_t*)"CMPTR_PUBLIC_KEY_COMMITMENT", 27);
    sha3_final(&ctx, (*public_key)->commitment, 32);
    
    // Derive verification key
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (*private_key)->seed, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (*private_key)->chain_code, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, (const uint8_t*)"CMPTR_VERIFICATION_KEY", 22);
    sha3_final(&ctx, (*public_key)->verification_key, 32);
    
    return true;
}