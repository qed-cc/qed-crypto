/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_COMMITMENTS_H
#define CMPTR_COMMITMENTS_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Constants
#define CMPTR_COMMIT_SIZE      32    // SHA3-256 commitment
#define CMPTR_COMMIT_MAX_SIZE  192000 // Max proof size (~190KB)

// Commitment types
typedef enum {
    CMPTR_COMMIT_MERKLE = 0,      // Standard Merkle commitment
    CMPTR_COMMIT_KATE,            // Kate polynomial commitment (SHA3-based)
    CMPTR_COMMIT_VERKLE,          // Verkle tree commitment
    CMPTR_COMMIT_TENSOR           // Tensor-based (for BaseFold)
} cmptr_commit_type_t;

// Forward declarations
typedef struct cmptr_commitment_scheme cmptr_commitment_scheme_t;
typedef struct cmptr_commitment cmptr_commitment_t;
typedef struct cmptr_commit_proof cmptr_commit_proof_t;
typedef struct cmptr_commit_batch cmptr_commit_batch_t;

// Scheme configuration
typedef struct {
    cmptr_commit_type_t type;
    size_t vector_size_hint;      // Expected vector size
    bool enable_updates;          // Support efficient updates
    bool enable_aggregation;      // Support proof aggregation
} cmptr_commit_config_t;

// Initialize commitment scheme
cmptr_commitment_scheme_t* cmptr_commit_scheme_new(const cmptr_commit_config_t* config);

// Commit to a vector of values
cmptr_commitment_t* cmptr_commit_vector(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t** values,
    const size_t* value_sizes,
    size_t count
);

// Open commitment at specific index
cmptr_commit_proof_t* cmptr_commit_open(
    cmptr_commitment_scheme_t* scheme,
    const cmptr_commitment_t* commitment,
    size_t index
);

// Verify opening
bool cmptr_commit_verify(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t commitment[CMPTR_COMMIT_SIZE],
    size_t index,
    const uint8_t* value,
    size_t value_size,
    const cmptr_commit_proof_t* proof
);

// Batch operations for efficiency
cmptr_commit_batch_t* cmptr_commit_batch_new(cmptr_commitment_scheme_t* scheme);

// Open multiple indices at once
bool cmptr_commit_batch_open(
    cmptr_commit_batch_t* batch,
    const cmptr_commitment_t* commitment,
    const size_t* indices,
    size_t count,
    cmptr_commit_proof_t** proofs_out
);

// Verify multiple openings
bool cmptr_commit_batch_verify(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t commitment[CMPTR_COMMIT_SIZE],
    const size_t* indices,
    const uint8_t** values,
    const size_t* value_sizes,
    const cmptr_commit_proof_t** proofs,
    size_t count
);

void cmptr_commit_batch_free(cmptr_commit_batch_t* batch);

// Update commitment (if enabled)
bool cmptr_commit_update(
    cmptr_commitment_scheme_t* scheme,
    cmptr_commitment_t* commitment,
    size_t index,
    const uint8_t* new_value,
    size_t new_value_size
);

// Get commitment value
bool cmptr_commit_get_value(
    const cmptr_commitment_t* commitment,
    uint8_t commitment_out[CMPTR_COMMIT_SIZE]
);

// Aggregated proofs (if enabled)
cmptr_commit_proof_t* cmptr_commit_aggregate_proofs(
    cmptr_commitment_scheme_t* scheme,
    const cmptr_commit_proof_t** proofs,
    size_t count
);

// Proof serialization
bool cmptr_commit_proof_export(
    const cmptr_commit_proof_t* proof,
    uint8_t* out,
    size_t* out_len
);

cmptr_commit_proof_t* cmptr_commit_proof_import(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t* data,
    size_t data_len
);

// Commitment serialization
bool cmptr_commit_export(
    const cmptr_commitment_t* commitment,
    uint8_t* out,
    size_t* out_len
);

cmptr_commitment_t* cmptr_commit_import(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t* data,
    size_t data_len
);

// Statistics
typedef struct {
    size_t vector_size;
    size_t proof_size_avg;
    size_t commitment_size;
    uint64_t total_openings;
    uint64_t total_updates;
    double verification_time_avg_ms;
} cmptr_commit_stats_t;

void cmptr_commit_get_stats(
    const cmptr_commitment_scheme_t* scheme,
    cmptr_commit_stats_t* stats_out
);

// Free resources
void cmptr_commit_scheme_free(cmptr_commitment_scheme_t* scheme);
void cmptr_commit_free(cmptr_commitment_t* commitment);
void cmptr_commit_proof_free(cmptr_commit_proof_t* proof);

// Utility: Commit to single value (convenience)
bool cmptr_commit_single(
    cmptr_commitment_scheme_t* scheme,
    const uint8_t* value,
    size_t value_size,
    uint8_t commitment_out[CMPTR_COMMIT_SIZE]
);

// Utility: Get proof size estimate
size_t cmptr_commit_proof_size_estimate(
    const cmptr_commitment_scheme_t* scheme,
    size_t vector_size,
    size_t indices_count
);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_COMMITMENTS_H