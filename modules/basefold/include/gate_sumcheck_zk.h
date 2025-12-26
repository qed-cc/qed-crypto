#ifndef GATE_SUMCHECK_ZK_H
#define GATE_SUMCHECK_ZK_H

/**
 * @file gate_sumcheck_zk.h
 * @brief Zero-knowledge extensions for gate sumcheck verification
 * 
 * Provides functions to generate deterministic masks for sumcheck rounds
 * ensuring both prover and verifier apply identical transformations.
 */

#include <stdint.h>
#include "gf128.h"
#include "sha3.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Generate deterministic round mask for zero-knowledge
 * 
 * Both prover and verifier use this function to generate identical masks
 * for each sumcheck round, ensuring verification succeeds while maintaining
 * zero-knowledge property.
 * 
 * @param zk_seed 32-byte seed for deterministic randomness
 * @param round Current sumcheck round (0 to d-1)
 * @param eval_point Evaluation point (0 or 1 for univariate)
 * @return Deterministic mask value
 */
static inline gf128_t gate_sumcheck_generate_round_mask(
    const uint8_t* zk_seed,
    size_t round,
    int eval_point)
{
    if (!zk_seed) {
        // No masking if ZK is disabled
        return gf128_zero();
    }
    
    // Create unique hash input for this round and evaluation point
    uint8_t hash_input[64];
    memcpy(hash_input, zk_seed, 32);
    memcpy(hash_input + 32, "ROUND_MASK", 10);
    hash_input[42] = (uint8_t)round;
    hash_input[43] = (uint8_t)eval_point;
    
    // Zero out remaining bytes
    memset(hash_input + 44, 0, 20);
    
    // Hash to generate mask
    uint8_t hash_output[32];
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, hash_input, 64);
    sha3_final(&ctx, hash_output, 32);
    
    // Convert to GF128
    return gf128_from_bytes(hash_output);
}

/**
 * @brief Check if zero-knowledge is enabled for verification
 * 
 * @param has_zk Flag from proof header indicating ZK is enabled
 * @param zk_seed Seed from proof header (must be non-zero)
 * @return true if ZK masking should be applied
 */
static inline bool gate_sumcheck_zk_enabled(uint8_t has_zk, const uint8_t* zk_seed) {
    if (!has_zk || !zk_seed) {
        return false;
    }
    
    // Check seed is not all zeros
    for (int i = 0; i < 16; i++) {
        if (zk_seed[i] != 0) {
            return true;
        }
    }
    
    return false;
}

#ifdef __cplusplus
}
#endif

#endif /* GATE_SUMCHECK_ZK_H */