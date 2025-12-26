/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_SIGNATURES_H
#define CMPTR_SIGNATURES_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// Forward declarations
typedef struct cmptr_private_key cmptr_private_key_t;
typedef struct cmptr_public_key cmptr_public_key_t;
typedef struct cmptr_signature cmptr_signature_t;
typedef struct cmptr_aggregated_signature cmptr_aggregated_signature_t;
typedef struct cmptr_sig_system cmptr_sig_system_t;

// Key pair management
cmptr_sig_system_t* cmptr_sig_init(void);
void cmptr_sig_free(cmptr_sig_system_t* system);

// Generate a new key pair
bool cmptr_keygen(cmptr_sig_system_t* system, 
                  cmptr_private_key_t** private_key,
                  cmptr_public_key_t** public_key);

// Sign a message with STARK proof
cmptr_signature_t* cmptr_sign(cmptr_sig_system_t* system,
                              const cmptr_private_key_t* private_key,
                              const uint8_t* message,
                              size_t message_len);

// Verify a single signature
bool cmptr_verify(cmptr_sig_system_t* system,
                  const cmptr_public_key_t* public_key,
                  const uint8_t* message,
                  size_t message_len,
                  const cmptr_signature_t* signature);

// Aggregate multiple signatures into one recursive proof
cmptr_aggregated_signature_t* cmptr_aggregate(cmptr_sig_system_t* system,
                                              const cmptr_signature_t** signatures,
                                              size_t num_signatures);

// Verify an aggregated signature against multiple public keys and messages
bool cmptr_verify_aggregated(cmptr_sig_system_t* system,
                             const cmptr_public_key_t** public_keys,
                             const uint8_t** messages,
                             const size_t* message_lens,
                             size_t num_messages,
                             const cmptr_aggregated_signature_t* agg_signature);

// Serialization functions
size_t cmptr_signature_size(const cmptr_signature_t* sig);
size_t cmptr_aggregated_signature_size(const cmptr_aggregated_signature_t* agg_sig);
size_t cmptr_public_key_size(const cmptr_public_key_t* public_key);
size_t cmptr_private_key_size(const cmptr_private_key_t* private_key);

bool cmptr_signature_serialize(const cmptr_signature_t* sig, uint8_t* buffer, size_t buffer_len);
bool cmptr_aggregated_signature_serialize(const cmptr_aggregated_signature_t* agg_sig, uint8_t* buffer, size_t buffer_len);
bool cmptr_public_key_serialize(const cmptr_public_key_t* public_key, uint8_t* buffer, size_t buffer_len);
bool cmptr_private_key_serialize(const cmptr_private_key_t* private_key, uint8_t* buffer, size_t buffer_len);

cmptr_signature_t* cmptr_signature_deserialize(const uint8_t* buffer, size_t buffer_len);
cmptr_aggregated_signature_t* cmptr_aggregated_signature_deserialize(const uint8_t* buffer, size_t buffer_len);
cmptr_public_key_t* cmptr_public_key_deserialize(const uint8_t* buffer, size_t buffer_len);
cmptr_private_key_t* cmptr_private_key_deserialize(const uint8_t* buffer, size_t buffer_len);

// Memory management
void cmptr_signature_free(cmptr_signature_t* sig);
void cmptr_aggregated_signature_free(cmptr_aggregated_signature_t* agg_sig);
void cmptr_public_key_free(cmptr_public_key_t* public_key);
void cmptr_private_key_free(cmptr_private_key_t* private_key);

// Performance metrics
typedef struct {
    double sign_time_ms;
    double verify_time_ms;
    double aggregate_time_ms;
    double verify_aggregated_time_ms;
    size_t signature_size_bytes;
    size_t aggregated_signature_size_bytes;
} cmptr_sig_metrics_t;

cmptr_sig_metrics_t cmptr_sig_get_metrics(const cmptr_sig_system_t* system);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_SIGNATURES_H