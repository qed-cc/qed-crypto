/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

// Initialize the Cmptr Signatures system
cmptr_sig_system_t* cmptr_sig_init(void) {
    cmptr_sig_system_t* system = calloc(1, sizeof(cmptr_sig_system_t));
    if (!system) {
        return NULL;
    }
    
    // Initialize BaseFold RAA configuration for signatures
    system->config = basefold_raa_config_init();
    if (!system->config) {
        free(system);
        return NULL;
    }
    
    // Configure for SHA3-256 circuits (AXIOM A001: Only SHA3)
    basefold_raa_config_set_field(system->config, FIELD_GF128);
    basefold_raa_config_set_security_level(system->config, 121); // Max achievable
    basefold_raa_config_enable_zk(system->config, true); // AXIOM A002: Always ZK
    
    // Create prover and verifier instances
    system->prover = basefold_raa_prover_init(system->config);
    system->verifier = basefold_raa_verifier_init(system->config);
    
    if (!system->prover || !system->verifier) {
        basefold_raa_prover_free(system->prover);
        basefold_raa_verifier_free(system->verifier);
        basefold_raa_config_free(system->config);
        free(system);
        return NULL;
    }
    
    // Initialize metrics
    memset(&system->metrics, 0, sizeof(system->metrics));
    
    return system;
}

// Free the Cmptr Signatures system
void cmptr_sig_free(cmptr_sig_system_t* system) {
    if (!system) return;
    
    basefold_raa_prover_free(system->prover);
    basefold_raa_verifier_free(system->verifier);
    basefold_raa_config_free(system->config);
    free(system);
}

// Hash a message using SHA3-256 (AXIOM A001)
void cmptr_hash_message(const uint8_t* message, size_t message_len, uint8_t* hash_out) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, message, message_len);
    sha3_final(&ctx, hash_out, 32);
}

// Hash a public key using SHA3-256
void cmptr_hash_public_key(const cmptr_public_key_t* public_key, uint8_t* hash_out) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, public_key->commitment, CMPTR_SIG_HASH_SIZE);
    sha3_update(&ctx, public_key->verification_key, CMPTR_SIG_HASH_SIZE);
    sha3_final(&ctx, hash_out, 32);
}

// Get performance metrics
cmptr_metrics_t cmptr_get_metrics(const cmptr_sig_system_t* system) {
    cmptr_metrics_t metrics = {0};
    
    if (system->metrics.sign_count > 0) {
        metrics.sign_time_ms = system->metrics.total_sign_time / system->metrics.sign_count;
    }
    
    if (system->metrics.verify_count > 0) {
        metrics.verify_time_ms = system->metrics.total_verify_time / system->metrics.verify_count;
    }
    
    if (system->metrics.aggregate_count > 0) {
        metrics.aggregate_time_ms = system->metrics.total_aggregate_time / system->metrics.aggregate_count;
    }
    
    if (system->metrics.verify_aggregated_count > 0) {
        metrics.verify_aggregated_time_ms = system->metrics.total_verify_aggregated_time / 
                                           system->metrics.verify_aggregated_count;
    }
    
    // Expected sizes based on BaseFold RAA
    metrics.signature_size_bytes = 190 * 1024; // ~190KB per signature
    metrics.aggregated_signature_size_bytes = 190 * 1024; // Still ~190KB after aggregation!
    
    return metrics;
}

// Memory management for signatures
void cmptr_signature_free(cmptr_signature_t* sig) {
    if (!sig) return;
    basefold_proof_free(sig->stark_proof);
    free(sig);
}

void cmptr_aggregated_signature_free(cmptr_aggregated_signature_t* agg_sig) {
    if (!agg_sig) return;
    basefold_proof_free(agg_sig->recursive_proof);
    free(agg_sig->message_hashes);
    free(agg_sig->public_key_hashes);
    free(agg_sig);
}

void cmptr_public_key_free(cmptr_public_key_t* public_key) {
    if (!public_key) return;
    // Clear sensitive data
    memset(public_key, 0, sizeof(cmptr_public_key_t));
    free(public_key);
}

void cmptr_private_key_free(cmptr_private_key_t* private_key) {
    if (!private_key) return;
    // Clear sensitive data
    memset(private_key, 0, sizeof(cmptr_private_key_t));
    free(private_key);
}