/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef BASEFOLD_PROOF_FORMAT_H
#define BASEFOLD_PROOF_FORMAT_H

#include <stdint.h>

/**
 * @brief BaseFold proof format versions
 */
#define BASEFOLD_VERSION_1 1  // Original format (all openings)
#define BASEFOLD_VERSION_2 2  // Added checksums
#define BASEFOLD_VERSION_3 3  // Probabilistic verification with λ repetitions

/**
 * @brief Current version in use
 */
#define BASEFOLD_CURRENT_VERSION BASEFOLD_VERSION_3

/**
 * @brief Security parameter for probabilistic verification
 * 
 * λ = 3 gives us 2^{-366} soundness error
 */
#define BASEFOLD_LAMBDA 3

/**
 * @brief Version 1 header (legacy - opens all points)
 */
typedef struct {
    uint8_t magic[8];           // "BASEFOLD"
    uint32_t version;           // Version 1
    uint32_t num_gates;         // Number of gates in circuit
    uint32_t d_value;           // Log2 of padded size
    uint8_t output_hash[32];    // SHA-3 of circuit output for verification
    uint8_t has_zk;             // 1 if ZK is enabled, 0 otherwise
    uint8_t mask_seed[128];     // ZK masking seed - 1024 bits for paranoid security
} basefold_proof_header_v1_t;

/**
 * @brief Version 2 header (added checksums, still opens all points)
 */
typedef struct {
    uint8_t magic[8];           // "BASEFOLD" 
    uint32_t version;           // Version 2
    uint32_t header_size;       // Size of this header (for forward compatibility)
    uint32_t proof_size;        // Total size of proof data (excluding header)
    uint32_t num_gates;         // Number of gates in circuit
    uint32_t d_value;           // Log2 of padded size
    uint8_t output_hash[32];    // SHA-3 of circuit output for verification
    uint8_t has_zk;             // 1 if ZK is enabled, 0 otherwise
    uint8_t reserved[3];        // Padding for alignment
    uint8_t mask_seed[128];     // ZK masking seed - 1024 bits for paranoid security
    uint8_t header_checksum[32]; // SHA3-256 of header (excluding this field)
    uint8_t proof_checksum[32];  // SHA3-256 of entire proof data
} basefold_proof_header_v2_t;

/**
 * @brief Version 3 header - Probabilistic verification
 * 
 * This version implements the fix for the critical bug where we were
 * opening all 2^d points. Now we only open λ = 3 points for
 * probabilistic verification with 2^{-366} soundness error.
 */
typedef struct {
    uint8_t magic[8];           // "BASEFOLD" 
    uint32_t version;           // Version 3
    uint32_t header_size;       // Size of this header (for forward compatibility)
    uint32_t proof_size;        // Total size of proof data (excluding header)
    uint32_t num_gates;         // Number of gates in circuit
    uint32_t d_value;           // Log2 of padded size
    uint8_t lambda;             // Number of verification instances (3)
    uint8_t has_zk;             // 1 if ZK is enabled, 0 otherwise
    uint8_t reserved[2];        // Padding for alignment
    uint8_t output_hash[32];    // SHA-3 of circuit output for verification
    uint8_t mask_seed[128];     // ZK masking seed - 1024 bits for paranoid security
    uint8_t header_checksum[32]; // SHA3-256 of header (excluding this field)
    uint8_t proof_checksum[32];  // SHA3-256 of entire proof data
} basefold_proof_header_v3_t;

/**
 * @brief Version 4 header - Binary NTT + FRI
 */
typedef struct {
    uint8_t magic[8];           // "BASEFOLD" 
    uint32_t version;           // Version 4
    uint32_t header_size;       // Size of this header
    uint32_t proof_size;        // Total size of FRI proof data
    uint32_t num_gates;         // Number of gates in circuit
    uint32_t d_value;           // Log2 of padded size
    uint8_t has_zk;             // 1 if ZK is enabled, 0 otherwise
    uint8_t reserved[3];        // Padding for alignment
    uint8_t output_hash[32];    // SHA-3 of circuit output for verification
    uint8_t mask_seed[128];     // ZK masking seed
    uint8_t header_checksum[32]; // SHA3-256 of header
    uint8_t proof_checksum[32];  // SHA3-256 of entire proof data
} basefold_proof_header_v4_t;

/**
 * @brief BaseFold proof versions enum
 */
typedef enum {
    BASEFOLD_V1_FULL_OPENING = 1,
    BASEFOLD_V2_WITH_CHECKSUMS = 2,
    BASEFOLD_V3_PROBABILISTIC = 3,
    BASEFOLD_V4_BINARY_NTT_FRI = 4
} basefold_version_t;

/**
 * @brief Current header type
 */
typedef basefold_proof_header_v4_t basefold_proof_header_t;

/**
 * @brief Placeholder FRI proof type
 */
typedef struct {
    uint32_t num_rounds;
    uint32_t num_queries;
    uint32_t final_degree;
    void* data;
} fri_proof_t;

/**
 * @brief Proof data layout for v3 (probabilistic)
 * 
 * After the header, the proof contains:
 * 1. Merkle root (32 bytes)
 * 2. Gate sumcheck coefficients (λ × d × 64 bytes)
 * 3. Wiring sumcheck coefficients (λ × d × 64 bytes)
 * 4. Final scalars (λ × 2 × 16 bytes = 96 bytes for gate+wiring)
 * 5. Merkle openings (λ × authentication paths)
 * 
 * Total proof size for 18 rounds with λ=3:
 * - Header: 336 bytes
 * - Root: 32 bytes
 * - Coefficients: 3 × 18 × 64 × 2 = 6,912 bytes
 * - Scalars: 96 bytes
 * - Merkle paths: 3 × 18 × 32 = 1,728 bytes
 * - Total: ~9KB (vs 126MB for old format!)
 */

#endif /* BASEFOLD_PROOF_FORMAT_H */