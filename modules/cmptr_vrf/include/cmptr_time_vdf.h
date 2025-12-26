/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_TIME_VDF_H
#define CMPTR_TIME_VDF_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file cmptr_time_vdf.h
 * @brief Recursive STARK VDF for proving computational age
 * 
 * This module implements a Verifiable Delay Function using recursive STARKs
 * that can prove "this computation must be at least X time old" with:
 * - Constant-size proofs (190KB) regardless of duration
 * - Constant verification time (8ms) for any time period
 * - Checkpointing for fault tolerance
 * - Composable proofs from multiple parties
 */

/* Constants */
#define CMPTR_VDF_HASH_SIZE         32      /* SHA3-256 */
#define CMPTR_VDF_PROOF_SIZE        192000  /* ~190KB STARK proof */
#define CMPTR_VDF_CHECKPOINT_HOUR   3600    /* Checkpoint every hour */

/* VDF parameters */
typedef struct {
    double iterations_per_second;    /* Sequential hash rate */
    uint32_t checkpoint_interval;    /* Seconds between checkpoints */
    bool enable_compression;         /* Compress old checkpoints */
    bool enable_parallel_proving;    /* Use multiple cores for proofs */
} cmptr_vdf_config_t;

/* Forward declarations */
typedef struct cmptr_vdf_system cmptr_vdf_system_t;
typedef struct cmptr_vdf_checkpoint cmptr_vdf_checkpoint_t;
typedef struct cmptr_vdf_proof cmptr_vdf_proof_t;

/* Time periods for aggregation */
typedef enum {
    CMPTR_VDF_PERIOD_HOUR = 0,
    CMPTR_VDF_PERIOD_DAY,
    CMPTR_VDF_PERIOD_MONTH,
    CMPTR_VDF_PERIOD_YEAR,
    CMPTR_VDF_PERIOD_CUSTOM
} cmptr_vdf_period_t;

/* Checkpoint data */
typedef struct {
    uint8_t start_hash[CMPTR_VDF_HASH_SIZE];
    uint8_t end_hash[CMPTR_VDF_HASH_SIZE];
    uint64_t iterations;
    uint64_t timestamp;
    cmptr_vdf_proof_t* proof;  /* Individual checkpoint proof */
} cmptr_vdf_checkpoint_data_t;

/**
 * Initialize VDF system
 * 
 * @param config Configuration (NULL for defaults)
 * @return VDF system instance
 */
cmptr_vdf_system_t* cmptr_vdf_init(const cmptr_vdf_config_t* config);

/**
 * Start VDF computation from seed
 * 
 * @param system VDF system
 * @param seed Initial seed value
 * @param seed_len Seed length
 * @return Starting checkpoint
 */
cmptr_vdf_checkpoint_t* cmptr_vdf_start(
    cmptr_vdf_system_t* system,
    const uint8_t* seed,
    size_t seed_len
);

/**
 * Continue VDF computation for specified duration
 * 
 * @param system VDF system
 * @param checkpoint Current checkpoint
 * @param duration_seconds Time to compute
 * @return New checkpoint after duration
 */
cmptr_vdf_checkpoint_t* cmptr_vdf_compute(
    cmptr_vdf_system_t* system,
    const cmptr_vdf_checkpoint_t* checkpoint,
    uint64_t duration_seconds
);

/**
 * Generate checkpoint at current position
 * 
 * @param system VDF system
 * @param current_hash Current hash value
 * @param iterations Iterations completed
 * @param timestamp Current timestamp
 * @return Checkpoint with proof
 */
cmptr_vdf_checkpoint_t* cmptr_vdf_checkpoint(
    cmptr_vdf_system_t* system,
    const uint8_t current_hash[CMPTR_VDF_HASH_SIZE],
    uint64_t iterations,
    uint64_t timestamp
);

/**
 * Aggregate multiple checkpoints into higher-level proof
 * 
 * @param system VDF system
 * @param checkpoints Array of checkpoints to aggregate
 * @param count Number of checkpoints
 * @param period Time period type (hour->day, day->month, etc)
 * @return Aggregated proof
 */
cmptr_vdf_proof_t* cmptr_vdf_aggregate(
    cmptr_vdf_system_t* system,
    const cmptr_vdf_checkpoint_t** checkpoints,
    size_t count,
    cmptr_vdf_period_t period
);

/**
 * Verify VDF proof for time duration
 * 
 * @param system VDF system
 * @param start_hash Expected starting hash
 * @param end_hash Expected ending hash
 * @param min_iterations Minimum iterations required
 * @param proof VDF proof
 * @return true if proof is valid
 */
bool cmptr_vdf_verify(
    cmptr_vdf_system_t* system,
    const uint8_t start_hash[CMPTR_VDF_HASH_SIZE],
    const uint8_t end_hash[CMPTR_VDF_HASH_SIZE],
    uint64_t min_iterations,
    const cmptr_vdf_proof_t* proof
);

/**
 * Verify proof represents minimum time duration
 * 
 * @param system VDF system
 * @param proof VDF proof
 * @param min_seconds Minimum seconds that must have passed
 * @return true if proof represents at least min_seconds
 */
bool cmptr_vdf_verify_age(
    cmptr_vdf_system_t* system,
    const cmptr_vdf_proof_t* proof,
    uint64_t min_seconds
);

/**
 * Combine proofs from different time periods
 * 
 * @param system VDF system
 * @param proof1 First proof (earlier time)
 * @param proof2 Second proof (later time)
 * @return Combined proof or NULL if they don't connect
 */
cmptr_vdf_proof_t* cmptr_vdf_combine(
    cmptr_vdf_system_t* system,
    const cmptr_vdf_proof_t* proof1,
    const cmptr_vdf_proof_t* proof2
);

/**
 * Export checkpoint for persistence
 */
bool cmptr_vdf_checkpoint_export(
    const cmptr_vdf_checkpoint_t* checkpoint,
    uint8_t* out,
    size_t* out_len
);

cmptr_vdf_checkpoint_t* cmptr_vdf_checkpoint_import(
    cmptr_vdf_system_t* system,
    const uint8_t* data,
    size_t data_len
);

/**
 * Export/import proofs
 */
bool cmptr_vdf_proof_export(
    const cmptr_vdf_proof_t* proof,
    uint8_t* out,
    size_t* out_len
);

cmptr_vdf_proof_t* cmptr_vdf_proof_import(
    cmptr_vdf_system_t* system,
    const uint8_t* data,
    size_t data_len
);

/**
 * Get proof metadata
 */
typedef struct {
    uint64_t total_iterations;
    uint64_t start_timestamp;
    uint64_t end_timestamp;
    uint32_t checkpoint_count;
    cmptr_vdf_period_t highest_aggregation;
    size_t proof_size;
} cmptr_vdf_proof_info_t;

void cmptr_vdf_proof_info(
    const cmptr_vdf_proof_t* proof,
    cmptr_vdf_proof_info_t* info_out
);

/**
 * Free resources
 */
void cmptr_vdf_system_free(cmptr_vdf_system_t* system);
void cmptr_vdf_checkpoint_free(cmptr_vdf_checkpoint_t* checkpoint);
void cmptr_vdf_proof_free(cmptr_vdf_proof_t* proof);

/**
 * Utility: Calculate iterations for time duration
 * 
 * @param system VDF system
 * @param seconds Duration in seconds
 * @return Number of iterations
 */
uint64_t cmptr_vdf_iterations_for_duration(
    const cmptr_vdf_system_t* system,
    uint64_t seconds
);

/**
 * Utility: Estimate time for iterations
 * 
 * @param system VDF system
 * @param iterations Number of iterations
 * @return Estimated seconds
 */
double cmptr_vdf_duration_for_iterations(
    const cmptr_vdf_system_t* system,
    uint64_t iterations
);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_TIME_VDF_H */