/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_VRF_H
#define CMPTR_VRF_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Constants - all SHA3-256 based
#define CMPTR_VRF_SECRET_SIZE      32      // 256-bit secret key
#define CMPTR_VRF_PUBLIC_SIZE      32      // SHA3 of secret
#define CMPTR_VRF_PROOF_SIZE       192000  // ~190KB STARK proof
#define CMPTR_VRF_OUTPUT_SIZE      32      // 256-bit output

// Forward declarations
typedef struct cmptr_vrf_system cmptr_vrf_system_t;
typedef struct cmptr_vrf_secret cmptr_vrf_secret_t;
typedef struct cmptr_vrf_public cmptr_vrf_public_t;
typedef struct cmptr_vrf_proof cmptr_vrf_proof_t;

// VRF evaluation result
typedef struct {
    uint8_t output[CMPTR_VRF_OUTPUT_SIZE];  // Deterministic random output
    cmptr_vrf_proof_t* proof;               // Proof of correct evaluation
} cmptr_vrf_result_t;

// Initialize VRF system
cmptr_vrf_system_t* cmptr_vrf_init(void);

// Generate VRF key pair
bool cmptr_vrf_keygen(
    cmptr_vrf_system_t* system,
    cmptr_vrf_secret_t** secret_key,
    cmptr_vrf_public_t** public_key
);

// Evaluate VRF: produces output and proof
cmptr_vrf_result_t* cmptr_vrf_eval(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_secret_t* secret_key,
    const uint8_t* input,
    size_t input_len
);

// Verify VRF proof
bool cmptr_vrf_verify(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_public_t* public_key,
    const uint8_t* input,
    size_t input_len,
    const uint8_t output[CMPTR_VRF_OUTPUT_SIZE],
    const cmptr_vrf_proof_t* proof
);

// Extract output from result
bool cmptr_vrf_result_output(
    const cmptr_vrf_result_t* result,
    uint8_t output[CMPTR_VRF_OUTPUT_SIZE]
);

// Serialize/deserialize proof
bool cmptr_vrf_proof_export(
    const cmptr_vrf_proof_t* proof,
    uint8_t* out,
    size_t* out_len
);

cmptr_vrf_proof_t* cmptr_vrf_proof_import(
    cmptr_vrf_system_t* system,
    const uint8_t* data,
    size_t data_len
);

// Key serialization
bool cmptr_vrf_secret_export(
    const cmptr_vrf_secret_t* secret_key,
    uint8_t out[CMPTR_VRF_SECRET_SIZE]
);

cmptr_vrf_secret_t* cmptr_vrf_secret_import(
    cmptr_vrf_system_t* system,
    const uint8_t data[CMPTR_VRF_SECRET_SIZE]
);

bool cmptr_vrf_public_export(
    const cmptr_vrf_public_t* public_key,
    uint8_t out[CMPTR_VRF_PUBLIC_SIZE]
);

cmptr_vrf_public_t* cmptr_vrf_public_import(
    cmptr_vrf_system_t* system,
    const uint8_t data[CMPTR_VRF_PUBLIC_SIZE]
);

// Batch operations (for efficiency)
bool cmptr_vrf_batch_verify(
    cmptr_vrf_system_t* system,
    const cmptr_vrf_public_t** public_keys,
    const uint8_t** inputs,
    const size_t* input_lens,
    const uint8_t outputs[][CMPTR_VRF_OUTPUT_SIZE],
    const cmptr_vrf_proof_t** proofs,
    size_t count
);

// Free resources
void cmptr_vrf_system_free(cmptr_vrf_system_t* system);
void cmptr_vrf_secret_free(cmptr_vrf_secret_t* secret_key);
void cmptr_vrf_public_free(cmptr_vrf_public_t* public_key);
void cmptr_vrf_proof_free(cmptr_vrf_proof_t* proof);
void cmptr_vrf_result_free(cmptr_vrf_result_t* result);

// Utility: Domain separation for different VRF uses
void cmptr_vrf_domain_separate(
    cmptr_vrf_system_t* system,
    const char* domain
);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_VRF_H