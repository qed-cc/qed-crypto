/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_BASEFOLD_RAA_WRAPPER_H
#define CMPTR_POS_BASEFOLD_RAA_WRAPPER_H

#include "basefold_raa.h"
#include "circular_recursion.h"
#include <string.h>
#include <stdlib.h>

/**
 * @brief Wrapper to simplify basefold_raa_prove calls
 * 
 * This wrapper converts arbitrary witness data to GF128 format and
 * handles the configuration setup, matching the simplified API used
 * throughout the PoS code.
 * 
 * @param witness Witness data
 * @param witness_size Size of witness in bytes
 * @param tag Tag for the proof (unused, for compatibility)
 * @return Allocated proof or NULL on error
 */
static inline basefold_raa_proof_t* basefold_raa_prove_simple(
    const void* witness,
    size_t witness_size,
    const char* tag
) {
    (void)tag; /* Unused */
    
    /* Calculate number of GF128 elements needed */
    size_t num_elements = (witness_size + 15) / 16; /* Round up to 16-byte chunks */
    size_t num_vars = 0;
    size_t n = 1;
    while (n < num_elements) {
        n <<= 1;
        num_vars++;
    }
    
    /* Allocate GF128 witness */
    gf128_t* gf_witness = calloc(n, sizeof(gf128_t));
    if (!gf_witness) return NULL;
    
    /* Convert witness to GF128 elements */
    const uint8_t* bytes = (const uint8_t*)witness;
    for (size_t i = 0; i < witness_size; i += 16) {
        size_t chunk_size = (witness_size - i < 16) ? (witness_size - i) : 16;
        uint8_t chunk[16] = {0};
        memcpy(chunk, bytes + i, chunk_size);
        gf128_from_bytes(&gf_witness[i/16], chunk);
    }
    
    /* Configure proof */
    basefold_raa_config_t config = {
        .num_variables = num_vars,
        .security_level = 122,
        .enable_zk = 1,
        .num_threads = 0
    };
    
    /* Allocate proof structure */
    basefold_raa_proof_t* proof = calloc(1, sizeof(basefold_raa_proof_t));
    if (!proof) {
        free(gf_witness);
        return NULL;
    }
    
    /* Generate proof */
    int ret = basefold_raa_prove(gf_witness, &config, proof);
    free(gf_witness);
    
    if (ret != 0) {
        free(proof);
        return NULL;
    }
    
    return proof;
}

/**
 * @brief Wrapper to simplify basefold_raa_verify calls
 */
static inline bool basefold_raa_verify_simple(const basefold_raa_proof_t* proof) {
    if (!proof) return false;
    
    /* Reconstruct config from proof metadata */
    basefold_raa_config_t config = {
        .num_variables = proof->num_sumcheck_rounds,
        .security_level = 122,
        .enable_zk = (proof->randomizer_coeffs != NULL),
        .num_threads = 0
    };
    
    return basefold_raa_verify(proof, &config) == 0;
}

/* Compatibility macros for cleaner code */
#define basefold_raa_prove(witness, size, tag) basefold_raa_prove_simple(witness, size, tag)
#define basefold_raa_verify(proof) basefold_raa_verify_simple(proof)

#endif /* CMPTR_POS_BASEFOLD_RAA_WRAPPER_H */