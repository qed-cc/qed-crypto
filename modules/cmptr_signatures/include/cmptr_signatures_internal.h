/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_SIGNATURES_INTERNAL_H
#define CMPTR_SIGNATURES_INTERNAL_H

#include "cmptr_signatures.h"
#include "basefold_raa.h"
#include "../../sha3/include/sha3.h"
#include "../../common/include/secure_random.h"
#include <time.h>

// SHA3-256 hash size
#define CMPTR_SIG_HASH_SIZE 32

// Internal structures
struct cmptr_private_key {
    uint8_t seed[CMPTR_SIG_HASH_SIZE];  // SHA3-256 of randomness
    uint8_t chain_code[CMPTR_SIG_HASH_SIZE];  // For deterministic derivation
};

struct cmptr_public_key {
    uint8_t commitment[CMPTR_SIG_HASH_SIZE];  // SHA3-256 commitment to private key
    uint8_t verification_key[CMPTR_SIG_HASH_SIZE];  // Additional verification data
};

// STARK signature contains the proof and auxiliary data
struct cmptr_signature {
    basefold_proof_t* stark_proof;  // The actual STARK proof
    uint8_t message_hash[CMPTR_SIG_HASH_SIZE];  // SHA3-256 of message
    uint8_t public_key_hash[CMPTR_SIG_HASH_SIZE];  // SHA3-256 of public key
    uint8_t nonce[CMPTR_SIG_HASH_SIZE];  // Randomness for zero-knowledge
    uint64_t timestamp;  // Unix timestamp
};

// Aggregated signature with recursive proof
struct cmptr_aggregated_signature {
    basefold_proof_t* recursive_proof;  // Single recursive STARK proof
    uint8_t aggregation_hash[CMPTR_SIG_HASH_SIZE];  // Hash of all inputs
    size_t num_signatures;  // Number of signatures aggregated
    uint8_t* message_hashes;  // Array of message hashes
    uint8_t* public_key_hashes;  // Array of public key hashes
};

struct cmptr_sig_system {
    basefold_raa_config_t* config;  // BaseFold RAA configuration
    basefold_raa_prover_t* prover;  // Prover instance
    basefold_raa_verifier_t* verifier;  // Verifier instance
    
    // Performance tracking
    struct {
        double total_sign_time;
        double total_verify_time;
        double total_aggregate_time;
        double total_verify_aggregated_time;
        size_t sign_count;
        size_t verify_count;
        size_t aggregate_count;
        size_t verify_aggregated_count;
    } metrics;
};

// Internal functions
bool cmptr_create_signing_circuit(const cmptr_private_key_t* private_key,
                                  const uint8_t* message_hash,
                                  uint8_t* witness_data,
                                  size_t* witness_size);

bool cmptr_create_aggregation_circuit(const cmptr_signature_t** signatures,
                                      size_t num_signatures,
                                      uint8_t* witness_data,
                                      size_t* witness_size);

void cmptr_hash_message(const uint8_t* message, size_t message_len, uint8_t* hash_out);
void cmptr_hash_public_key(const cmptr_public_key_t* public_key, uint8_t* hash_out);

#endif // CMPTR_SIGNATURES_INTERNAL_H