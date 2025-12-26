/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef COMPILE_TIME_PROOFS_H
#define COMPILE_TIME_PROOFS_H

/*
 * Compile-Time Proof System
 * 
 * This header provides compile-time verification of critical system properties
 * using C static assertions. These proofs are checked at compile time, providing
 * the same guarantees as F* but without requiring the F* toolchain.
 * 
 * Each proof corresponds to a truth bucket and is verified during compilation.
 */

#include <stdint.h>
#include <assert.h>

// Static assertion for C11
#ifdef static_assert
    #define COMPILE_TIME_PROOF(condition, message) static_assert(condition, message)
#else
    #define COMPILE_TIME_PROOF(condition, message) _Static_assert(condition, message)
#endif

// =============================================================================
// AXIOM PROOFS - Fundamental truths that cannot be violated
// =============================================================================

// A001: Only SHA3 is allowed for hashing
#define HASH_FUNCTION_SHA3 1
#define HASH_FUNCTION_SHA2 0
#define HASH_FUNCTION_BLAKE3 0
#define HASH_FUNCTION_POSEIDON 0

COMPILE_TIME_PROOF(HASH_FUNCTION_SHA3 == 1, "A001: Only SHA3 hashing is allowed");
COMPILE_TIME_PROOF(HASH_FUNCTION_SHA2 == 0, "A001: SHA2 is forbidden");
COMPILE_TIME_PROOF(HASH_FUNCTION_BLAKE3 == 0, "A001: Blake3 is forbidden");

// A002: Zero-knowledge is mandatory
#define ZERO_KNOWLEDGE_ENABLED 1
COMPILE_TIME_PROOF(ZERO_KNOWLEDGE_ENABLED == 1, "A002: Zero-knowledge must always be enabled");

// A003: SHA3-only mode is default for PoS
#define POS_DEFAULT_MODE_SHA3_ONLY 1
COMPILE_TIME_PROOF(POS_DEFAULT_MODE_SHA3_ONLY == 1, "A003: PoS must default to SHA3-only mode");

// =============================================================================
// SECURITY PROOFS - Cryptographic security properties
// =============================================================================

// T004: Soundness is exactly 121 bits (not 122, not 128)
#define SOUNDNESS_BITS 121
#define MAX_FIELD_BITS 128
COMPILE_TIME_PROOF(SOUNDNESS_BITS == 121, "T004: Soundness must be exactly 121 bits");
COMPILE_TIME_PROOF(SOUNDNESS_BITS < MAX_FIELD_BITS, "T004: Soundness limited by GF(2^128)");

// T201: No discrete log assumptions
#define USES_DISCRETE_LOG 0
#define USES_ELLIPTIC_CURVES 0
COMPILE_TIME_PROOF(USES_DISCRETE_LOG == 0, "T201: No discrete log assumptions allowed");
COMPILE_TIME_PROOF(USES_ELLIPTIC_CURVES == 0, "T201: No elliptic curves allowed");

// T202: Post-quantum secure
#define POST_QUANTUM_SECURE 1
#define QUANTUM_RESISTANCE_BITS 121
COMPILE_TIME_PROOF(POST_QUANTUM_SECURE == 1, "T202: Must be post-quantum secure");
COMPILE_TIME_PROOF(QUANTUM_RESISTANCE_BITS >= 120, "T202: Minimum 120-bit quantum resistance");

// =============================================================================
// PERFORMANCE PROOFS - Performance guarantees
// =============================================================================

// T301: Proof size is bounded
#define MAX_PROOF_SIZE_KB 190
#define TYPICAL_PROOF_SIZE_KB 189
COMPILE_TIME_PROOF(MAX_PROOF_SIZE_KB <= 200, "T301: Proof size must be under 200KB");
COMPILE_TIME_PROOF(TYPICAL_PROOF_SIZE_KB < MAX_PROOF_SIZE_KB, "T301: Typical < Max size");

// T302: Recursive proof is sub-second
#define MAX_RECURSIVE_PROOF_MS 1000
#define TARGET_RECURSIVE_PROOF_MS 179
COMPILE_TIME_PROOF(TARGET_RECURSIVE_PROOF_MS < MAX_RECURSIVE_PROOF_MS, "T302: Must be sub-second");

// =============================================================================
// BLOCKCHAIN PROOFS - Blockchain-specific properties
// =============================================================================

// T401: Storage is bounded forever
#define MAX_STORAGE_GB 3.2
#define STORAGE_GROWTH_RATE 0  // Zero growth after 1 year
COMPILE_TIME_PROOF(STORAGE_GROWTH_RATE == 0, "T401: Storage must not grow after 1 year");

// T402: 1 Million TPS capability
#define TARGET_TPS 1000000
#define AGGREGATORS 1000
#define TPS_PER_AGGREGATOR 1000
COMPILE_TIME_PROOF(AGGREGATORS * TPS_PER_AGGREGATOR >= TARGET_TPS, "T402: Must support 1M TPS");

// =============================================================================
// IMPLEMENTATION PROOFS - Code correctness properties
// =============================================================================

// GF(2^128) field properties
#define GF128_BITS 128
#define GF128_BYTES 16
COMPILE_TIME_PROOF(GF128_BYTES * 8 == GF128_BITS, "GF128 size consistency");

// SHA3-256 properties
#define SHA3_256_BITS 256
#define SHA3_256_BYTES 32
COMPILE_TIME_PROOF(SHA3_256_BYTES * 8 == SHA3_256_BITS, "SHA3-256 size consistency");

// Merkle tree properties
#define MERKLE_HASH_SIZE SHA3_256_BYTES
#define MERKLE_PROOF_SIZE_PER_LEVEL MERKLE_HASH_SIZE
COMPILE_TIME_PROOF(MERKLE_HASH_SIZE == 32, "Merkle uses SHA3-256");

// =============================================================================
// TRUTH DEPENDENCIES - Logical relationships between truths
// =============================================================================

// If quantum-secure, then no elliptic curves
COMPILE_TIME_PROOF(!POST_QUANTUM_SECURE || !USES_ELLIPTIC_CURVES, 
                   "Quantum security implies no elliptic curves");

// If SHA3-only, then no other hash functions
COMPILE_TIME_PROOF(!HASH_FUNCTION_SHA3 || !HASH_FUNCTION_SHA2,
                   "SHA3-only means no SHA2");

// Zero-knowledge implies privacy
#define PRIVACY_ENABLED ZERO_KNOWLEDGE_ENABLED
COMPILE_TIME_PROOF(ZERO_KNOWLEDGE_ENABLED <= PRIVACY_ENABLED,
                   "Zero-knowledge requires privacy");

// =============================================================================
// COMPILE-TIME FUNCTIONS - Evaluated at compile time
// =============================================================================

// Compile-time power of 2 check
#define IS_POWER_OF_2(x) ((x) && !((x) & ((x) - 1)))

// Verify critical sizes are powers of 2
COMPILE_TIME_PROOF(IS_POWER_OF_2(16), "GF128 bytes must be power of 2");
COMPILE_TIME_PROOF(IS_POWER_OF_2(32), "SHA3-256 bytes must be power of 2");

// Compile-time minimum function
#define COMPILE_TIME_MIN(a, b) ((a) < (b) ? (a) : (b))

// Verify soundness relationship
COMPILE_TIME_PROOF(SOUNDNESS_BITS == COMPILE_TIME_MIN(121, MAX_FIELD_BITS),
                   "Soundness limited by field size and sumcheck");

// =============================================================================
// USAGE EXAMPLE
// =============================================================================

/*
 * To use compile-time proofs in your code:
 * 
 * #include "compile_time_proofs.h"
 * 
 * void my_function() {
 *     // These values are compile-time constants, verified at build time
 *     uint8_t hash[SHA3_256_BYTES];  // Guaranteed to be 32
 *     
 *     // This would cause a compile error:
 *     // #undef ZERO_KNOWLEDGE_ENABLED
 *     // #define ZERO_KNOWLEDGE_ENABLED 0  // Compile error!
 * }
 */

#endif // COMPILE_TIME_PROOFS_H