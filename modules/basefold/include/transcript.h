/**
 * @file transcript.h
 * @brief Fiat-Shamir transcript for non-interactive zero-knowledge proofs
 * 
 * This module implements the Fiat-Shamir transform, converting interactive
 * proof protocols into non-interactive ones by using a cryptographic hash
 * function to generate verifier challenges.
 * 
 * SECURITY MODEL:
 * - Uses SHA3-256 as the random oracle
 * - Domain separation prevents cross-protocol attacks
 * - Sequential absorption ensures unique transcripts
 * - 128-bit security level for challenge generation
 * 
 * PROTOCOL FLOW:
 * 1. Initialize with seed and domain
 * 2. Absorb all public inputs and commitments
 * 3. Generate challenges when needed
 * 4. Repeat absorb/challenge for each round
 * 
 * SECURITY REQUIREMENTS:
 * - Never reuse transcripts between proofs
 * - Absorb all data in deterministic order
 * - Use domain separation for different protocols
 * - Include protocol version in domain tags
 */

#ifndef TRANSCRIPT_H
#define TRANSCRIPT_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Fiat-Shamir transcript state
 * 
 * Maintains running SHA3-256 digest state for accumulating
 * commitments and generating verifiable random challenges.
 */
typedef struct {
    uint8_t state[32];  /**< Running SHA3-256 digest */
} fiat_shamir_t;

/**
 * @brief Domain separation tags for different protocol phases
 * 
 * These tags ensure challenges from different phases cannot be
 * mixed, preventing cross-protocol attacks.
 * 
 * SECURITY FIX: Enhanced domain separation with protocol-specific context
 * Each tag now includes:
 * - Protocol name and version
 * - Field size (GF128)
 * - Specific phase identifier
 * - Protocol parameters when relevant
 */
#define FS_DOMAIN_INIT          "BASEFOLD_v2_GF128_INIT_2024"
#define FS_DOMAIN_GATE_SC       "BASEFOLD_v2_GF128_GATE_SUMCHECK"
#define FS_DOMAIN_WIRING_SC     "BASEFOLD_v2_GF128_WIRING_SUMCHECK"
#define FS_DOMAIN_MERKLE_OPEN   "BASEFOLD_v2_GF128_MERKLE_SHA3_256"
#define FS_DOMAIN_POLYNOMIAL_ZK "BASEFOLD_v2_GF128_POLY_ZK_VANISHING"
#define FS_DOMAIN_CHALLENGE     "BASEFOLD_v2_GF128_CHALLENGE_GEN"

// Additional domain tags for round-specific operations
#define FS_DOMAIN_ROUND_PREFIX  "BASEFOLD_v2_GF128_ROUND_"
#define FS_DOMAIN_COEFF_PREFIX  "BASEFOLD_v2_GF128_COEFF_"

/**
 * @brief Initialize Fiat-Shamir transcript with seed
 * 
 * Initializes the transcript with a 16-byte seed that establishes
 * the initial state. This seed is typically derived from the ZK
 * mask seed to ensure prover and verifier transcripts match.
 * 
 * SECURITY NOTE: The seed must have sufficient entropy (128 bits)
 * to prevent replay attacks and ensure unpredictability.
 * 
 * @param fs Transcript instance to initialize
 * @param seed 16-byte seed value (typically from mask_seed[0:16])
 */
void fs_init(fiat_shamir_t *fs, const uint8_t seed[16]);

/**
 * @brief Initialize transcript with domain separation
 * @param fs Transcript instance to initialize
 * @param seed 16-byte initial seed value
 * @param domain Domain separation tag
 * 
 * Initializes with both seed and domain tag for better separation.
 */
void fs_init_with_domain(fiat_shamir_t *fs, const uint8_t seed[16], const char *domain);

/**
 * @brief Absorb data into Fiat-Shamir transcript
 * 
 * Absorbs arbitrary data into the transcript state. This binding
 * operation ensures that all subsequent challenges depend on all
 * previously absorbed data.
 * 
 * USAGE RULES:
 * - Absorb all public data (commitments, statements)
 * - Never absorb secret data (witness, randomness)
 * - Maintain identical order in prover and verifier
 * - Each piece of data should be absorbed exactly once
 * 
 * COMMON ABSORPTIONS:
 * - Merkle tree roots (32 bytes)
 * - SumCheck coefficients (64 bytes per round)
 * - Public inputs/outputs
 * - Protocol parameters
 * 
 * @param fs Transcript instance
 * @param data Data to absorb
 * @param len Length of data in bytes
 */
void fs_absorb(fiat_shamir_t *fs, const void *data, size_t len);

/**
 * @brief Absorb data with domain separation
 * @param fs Transcript instance
 * @param domain Domain separation tag
 * @param data Data to absorb
 * @param len Length of data in bytes
 * 
 * Absorbs data with a domain tag to prevent cross-protocol attacks.
 */
void fs_absorb_with_domain(fiat_shamir_t *fs, const char *domain, 
                           const void *data, size_t len);

/**
 * @brief Generate random challenge from transcript
 * @param fs Transcript instance
 * @param out Buffer for 32-byte challenge output
 * 
 * Generates a public random scalar from the current transcript state.
 * Used for SumCheck challenges (r₁, r₂, ...) and other protocol
 * randomness requirements.
 */
void fs_challenge(fiat_shamir_t *fs, uint8_t out[32]);

/**
 * @brief Generate challenge with domain separation
 * @param fs Transcript instance
 * @param domain Domain separation tag
 * @param out Buffer for 32-byte challenge output
 * 
 * Generates challenge with explicit domain tag for better security.
 */
void fs_challenge_with_domain(fiat_shamir_t *fs, const char *domain, uint8_t out[32]);

#ifdef __cplusplus
}
#endif

#endif /* TRANSCRIPT_H */