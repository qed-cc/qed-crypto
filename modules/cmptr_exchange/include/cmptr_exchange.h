/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_EXCHANGE_H
#define CMPTR_EXCHANGE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Constants - all SHA3-256 based
#define CMPTR_EXCHANGE_PUBLIC_SIZE    192000  // ~190KB STARK proof
#define CMPTR_EXCHANGE_PRIVATE_SIZE   32      // 256-bit private key
#define CMPTR_EXCHANGE_SHARED_SIZE    32      // 256-bit shared secret
#define CMPTR_EXCHANGE_COMMIT_SIZE    32      // SHA3-256 commitment

// Forward declarations
typedef struct cmptr_exchange_system cmptr_exchange_system_t;
typedef struct cmptr_exchange_private cmptr_exchange_private_t;
typedef struct cmptr_exchange_public cmptr_exchange_public_t;
typedef struct cmptr_exchange_transcript cmptr_exchange_transcript_t;

// Exchange protocol phases
typedef enum {
    CMPTR_EXCHANGE_INIT = 0,
    CMPTR_EXCHANGE_COMMIT,
    CMPTR_EXCHANGE_REVEAL,
    CMPTR_EXCHANGE_DERIVE,
    CMPTR_EXCHANGE_COMPLETE
} cmptr_exchange_phase_t;

// Initialize exchange system
cmptr_exchange_system_t* cmptr_exchange_init(void);

// Generate ephemeral key pair
bool cmptr_exchange_keygen(
    cmptr_exchange_system_t* system,
    cmptr_exchange_private_t** private_key,
    cmptr_exchange_public_t** public_key
);

// Phase 1: Create commitment to public key
bool cmptr_exchange_commit(
    const cmptr_exchange_public_t* public_key,
    uint8_t commitment_out[CMPTR_EXCHANGE_COMMIT_SIZE]
);

// Phase 2: Reveal public key (STARK proof)
bool cmptr_exchange_reveal(
    const cmptr_exchange_public_t* public_key,
    uint8_t* proof_out,
    size_t* proof_len
);

// Phase 3: Derive shared secret
bool cmptr_exchange_derive(
    cmptr_exchange_system_t* system,
    const cmptr_exchange_private_t* private_key,
    const uint8_t* peer_proof,
    size_t peer_proof_len,
    uint8_t shared_secret_out[CMPTR_EXCHANGE_SHARED_SIZE]
);

// Verify commitment matches revealed key
bool cmptr_exchange_verify_commitment(
    const uint8_t commitment[CMPTR_EXCHANGE_COMMIT_SIZE],
    const uint8_t* proof,
    size_t proof_len
);

// Create authenticated transcript of exchange
cmptr_exchange_transcript_t* cmptr_exchange_transcript_new(void);

// Add message to transcript
void cmptr_exchange_transcript_add(
    cmptr_exchange_transcript_t* transcript,
    const char* label,
    const uint8_t* data,
    size_t len
);

// Finalize transcript into shared context
bool cmptr_exchange_transcript_finalize(
    cmptr_exchange_transcript_t* transcript,
    const uint8_t shared_secret[CMPTR_EXCHANGE_SHARED_SIZE],
    uint8_t context_out[32]
);

// Serialize/deserialize keys
bool cmptr_exchange_private_export(
    const cmptr_exchange_private_t* private_key,
    uint8_t out[CMPTR_EXCHANGE_PRIVATE_SIZE]
);

cmptr_exchange_private_t* cmptr_exchange_private_import(
    cmptr_exchange_system_t* system,
    const uint8_t data[CMPTR_EXCHANGE_PRIVATE_SIZE]
);

bool cmptr_exchange_public_export(
    const cmptr_exchange_public_t* public_key,
    uint8_t* out,
    size_t* out_len
);

cmptr_exchange_public_t* cmptr_exchange_public_import(
    cmptr_exchange_system_t* system,
    const uint8_t* data,
    size_t data_len
);

// Free resources
void cmptr_exchange_system_free(cmptr_exchange_system_t* system);
void cmptr_exchange_private_free(cmptr_exchange_private_t* private_key);
void cmptr_exchange_public_free(cmptr_exchange_public_t* public_key);
void cmptr_exchange_transcript_free(cmptr_exchange_transcript_t* transcript);

// Utility: Constant-time comparison
bool cmptr_exchange_ct_equal(const uint8_t* a, const uint8_t* b, size_t len);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_EXCHANGE_H