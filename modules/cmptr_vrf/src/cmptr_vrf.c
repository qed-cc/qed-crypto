/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_vrf.h"
#include "../../sha3/include/sha3.h"
#include "../../common/include/secure_random.h"
#include <stdlib.h>
#include <string.h>

// VRF system state
struct cmptr_vrf_system {
    char domain[64];  // Domain separation string
    uint32_t domain_len;
};

// Secret key
struct cmptr_vrf_secret {
    uint8_t key[CMPTR_VRF_SECRET_SIZE];
};

// Public key: SHA3(secret || "vrf_public")
struct cmptr_vrf_public {
    uint8_t key[CMPTR_VRF_PUBLIC_SIZE];
};

// VRF proof: In full implementation, this would be a STARK proof
struct cmptr_vrf_proof {
    uint8_t data[2048];  // Simulated proof (much smaller than real)
    size_t actual_size;
};

// Initialize VRF system
cmptr_vrf_system_t* cmptr_vrf_init(void) {
    cmptr_vrf_system_t* system = calloc(1, sizeof(cmptr_vrf_system_t));
    if (!system) return NULL;
    
    // Default domain
    strcpy(system->domain, "cmptr_vrf_v1");
    system->domain_len = strlen(system->domain);
    
    return system;
}

// Generate VRF key pair
bool cmptr_vrf_keygen(
    cmptr_vrf_system_t* system,
    cmptr_vrf_secret_t** secret_key,
    cmptr_vrf_public_t** public_key
) {
    if (!system || !secret_key || !public_key) return false;
    
    // Generate secret key
    *secret_key = calloc(1, sizeof(cmptr_vrf_secret_t));
    if (!*secret_key) return false;
    
    if (secure_random_bytes((*secret_key)->key, CMPTR_VRF_SECRET_SIZE) != SECURE_RANDOM_SUCCESS) {
        free(*secret_key);
        *secret_key = NULL;
        return false;
    }
    
    // Derive public key
    *public_key = calloc(1, sizeof(cmptr_vrf_public_t));
    if (!*public_key) {
        free(*secret_key);
        *secret_key = NULL;
        return false;
    }
    
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (*secret_key)->key, CMPTR_VRF_SECRET_SIZE);
    sha3_update(&ctx, (const uint8_t*)"vrf_public", 10);
    sha3_final(&ctx, (*public_key)->key, 32);
    
    return true;
}

// Evaluate VRF
cmptr_vrf_result_t* cmptr_vrf_eval(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_secret_t* secret_key,
    const uint8_t* input,
    size_t input_len
) {
    if (!system || !secret_key || !input) return NULL;
    
    cmptr_vrf_result_t* result = calloc(1, sizeof(cmptr_vrf_result_t));
    if (!result) return NULL;
    
    // Compute VRF output = SHA3(domain || secret || input)
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)system->domain, system->domain_len);
    sha3_update(&ctx, secret_key->key, CMPTR_VRF_SECRET_SIZE);
    sha3_update(&ctx, input, input_len);
    sha3_final(&ctx, result->output, 32);
    
    // Generate proof
    result->proof = calloc(1, sizeof(cmptr_vrf_proof_t));
    if (!result->proof) {
        free(result);
        return NULL;
    }
    
    // In full implementation:
    // 1. Create circuit that proves: "I know sk such that pk = SHA3(sk) AND output = SHA3(domain || sk || input)"
    // 2. Generate STARK proof using BaseFold RAA
    // 3. Proof is zero-knowledge and ~190KB
    
    // For now, simulate with commitment + signature
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"vrf_proof", 9);
    sha3_update(&ctx, secret_key->key, CMPTR_VRF_SECRET_SIZE);
    sha3_update(&ctx, input, input_len);
    sha3_update(&ctx, result->output, CMPTR_VRF_OUTPUT_SIZE);
    sha3_final(&ctx, result->proof->data, 32);
    
    // Add some padding to simulate proof size
    memset(result->proof->data + 32, 0xVF, 512);
    result->proof->actual_size = 544;
    
    return result;
}

// Verify VRF proof
bool cmptr_vrf_verify(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_public_t* public_key,
    const uint8_t* input,
    size_t input_len,
    const uint8_t output[CMPTR_VRF_OUTPUT_SIZE],
    const cmptr_vrf_proof_t* proof
) {
    if (!system || !public_key || !input || !output || !proof) return false;
    
    // In full implementation:
    // 1. Verify STARK proof
    // 2. Check that proof shows knowledge of sk where pk = SHA3(sk)
    // 3. Check that output = SHA3(domain || sk || input)
    
    // For simulation, just check that proof data looks reasonable
    return proof->actual_size > 32 && proof->data[0] != 0;
}

// Extract output
bool cmptr_vrf_result_output(
    const cmptr_vrf_result_t* result,
    uint8_t output[CMPTR_VRF_OUTPUT_SIZE]
) {
    if (!result || !output) return false;
    memcpy(output, result->output, CMPTR_VRF_OUTPUT_SIZE);
    return true;
}

// Export proof
bool cmptr_vrf_proof_export(
    const cmptr_vrf_proof_t* proof,
    uint8_t* out,
    size_t* out_len
) {
    if (!proof || !out || !out_len) return false;
    memcpy(out, proof->data, proof->actual_size);
    *out_len = proof->actual_size;
    return true;
}

// Import proof
cmptr_vrf_proof_t* cmptr_vrf_proof_import(
    cmptr_vrf_system_t* system,
    const uint8_t* data,
    size_t data_len
) {
    if (!system || !data || data_len > sizeof(((cmptr_vrf_proof_t*)0)->data)) return NULL;
    
    cmptr_vrf_proof_t* proof = calloc(1, sizeof(cmptr_vrf_proof_t));
    if (!proof) return NULL;
    
    memcpy(proof->data, data, data_len);
    proof->actual_size = data_len;
    
    return proof;
}

// Export secret key
bool cmptr_vrf_secret_export(
    const cmptr_vrf_secret_t* secret_key,
    uint8_t out[CMPTR_VRF_SECRET_SIZE]
) {
    if (!secret_key || !out) return false;
    memcpy(out, secret_key->key, CMPTR_VRF_SECRET_SIZE);
    return true;
}

// Import secret key
cmptr_vrf_secret_t* cmptr_vrf_secret_import(
    cmptr_vrf_system_t* system,
    const uint8_t data[CMPTR_VRF_SECRET_SIZE]
) {
    if (!system || !data) return NULL;
    
    cmptr_vrf_secret_t* secret = calloc(1, sizeof(cmptr_vrf_secret_t));
    if (!secret) return NULL;
    
    memcpy(secret->key, data, CMPTR_VRF_SECRET_SIZE);
    return secret;
}

// Export public key
bool cmptr_vrf_public_export(
    const cmptr_vrf_public_t* public_key,
    uint8_t out[CMPTR_VRF_PUBLIC_SIZE]
) {
    if (!public_key || !out) return false;
    memcpy(out, public_key->key, CMPTR_VRF_PUBLIC_SIZE);
    return true;
}

// Import public key
cmptr_vrf_public_t* cmptr_vrf_public_import(
    cmptr_vrf_system_t* system,
    const uint8_t data[CMPTR_VRF_PUBLIC_SIZE]
) {
    if (!system || !data) return NULL;
    
    cmptr_vrf_public_t* public = calloc(1, sizeof(cmptr_vrf_public_t));
    if (!public) return NULL;
    
    memcpy(public->key, data, CMPTR_VRF_PUBLIC_SIZE);
    return public;
}

// Batch verify (simplified for demo)
bool cmptr_vrf_batch_verify(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_public_t** public_keys,
    const uint8_t** inputs,
    const size_t* input_lens,
    const uint8_t outputs[][CMPTR_VRF_OUTPUT_SIZE],
    const cmptr_vrf_proof_t** proofs,
    size_t count
) {
    if (!system || count == 0) return false;
    
    // In full implementation: batch verification with single STARK proof
    // For now, verify each individually
    for (size_t i = 0; i < count; i++) {
        if (!cmptr_vrf_verify(system, public_keys[i], inputs[i], input_lens[i], 
                             outputs[i], proofs[i])) {
            return false;
        }
    }
    
    return true;
}

// Free resources
void cmptr_vrf_system_free(cmptr_vrf_system_t* system) {
    if (!system) return;
    memset(system, 0, sizeof(*system));
    free(system);
}

void cmptr_vrf_secret_free(cmptr_vrf_secret_t* secret_key) {
    if (!secret_key) return;
    memset(secret_key->key, 0, sizeof(secret_key->key));
    free(secret_key);
}

void cmptr_vrf_public_free(cmptr_vrf_public_t* public_key) {
    if (!public_key) return;
    free(public_key);
}

void cmptr_vrf_proof_free(cmptr_vrf_proof_t* proof) {
    if (!proof) return;
    memset(proof->data, 0, sizeof(proof->data));
    free(proof);
}

void cmptr_vrf_result_free(cmptr_vrf_result_t* result) {
    if (!result) return;
    if (result->proof) {
        cmptr_vrf_proof_free(result->proof);
    }
    free(result);
}

// Domain separation
void cmptr_vrf_domain_separate(
    cmptr_vrf_system_t* system,
    const char* domain
) {
    if (!system || !domain) return;
    
    size_t len = strlen(domain);
    if (len >= sizeof(system->domain)) len = sizeof(system->domain) - 1;
    
    memcpy(system->domain, domain, len);
    system->domain[len] = '\0';
    system->domain_len = len;
}