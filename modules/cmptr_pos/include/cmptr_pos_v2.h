/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_V2_H
#define CMPTR_POS_V2_H

#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <pthread.h>
#include "cmptr_pos.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Protocol version for upgradeability */
#define CMPTR_POS_PROTOCOL_VERSION 2
#define CMPTR_POS_MIN_SUPPORTED_VERSION 1

/* Module versions - ALL use SHA3 exclusively for post-quantum security */
typedef enum {
    /* Snapshot modules (SHA3-based commitments only) */
    SNAPSHOT_MODULE_SHA3_VERKLE_V1 = 1,      /* SHA3-based Verkle tree */
    SNAPSHOT_MODULE_SHA3_MERKLE_V2 = 2,      /* Pure SHA3 Merkle tree */
    
    /* VRF modules (hash-based only, no elliptic curves/lattices) */
    VRF_MODULE_SHA3_V1 = 1,                  /* SHA3-based VRF */
    VRF_MODULE_SHA3_ENHANCED_V2 = 2,         /* SHA3 VRF with aggregation */
    
    /* Ordering modules (unchanged - they orchestrate, don't do crypto) */
    ORDERING_MODULE_MYSTICETI_V1 = 1,
    ORDERING_MODULE_BULLSHARK_V2 = 2,        /* Future */
    ORDERING_MODULE_HOTSTUFF_V3 = 3,         /* Future */
    
    /* Proof modules (SHA3-based proofs only) */
    PROOF_MODULE_BASEFOLD_SHA3_V1 = 1,      /* BaseFold with SHA3 */
    PROOF_MODULE_SHA3_STARK_V2 = 2,         /* Pure SHA3 STARKs */
    PROOF_MODULE_SHA3_FRACTAL_V3 = 3        /* SHA3 fractal proofs */
} module_version_t;

/* Module types for registry */
typedef enum {
    MODULE_TYPE_SNAPSHOT,
    MODULE_TYPE_VRF,
    MODULE_TYPE_ORDERING,
    MODULE_TYPE_PROOF
} module_type_t;

/* Upgrade state tracking */
typedef struct {
    bool is_upgrading;
    time_t start_time;
    time_t end_time;
    uint32_t completed_count;
    pthread_mutex_t upgrade_mutex;
} upgrade_state_t;

/* Consensus mode for optimization */
typedef enum {
    CONSENSUS_MODE_NORMAL,         /* Standard 6-phase */
    CONSENSUS_MODE_FAST_PATH,      /* Optimistic 2-phase */
    CONSENSUS_MODE_STREAMING,      /* Continuous DAG */
    CONSENSUS_MODE_RECOVERY        /* Byzantine recovery */
} consensus_mode_t;

/* Versioned module interface */
typedef struct {
    uint32_t version;
    const char* name;
    void* (*init)(void* config);
    void (*destroy)(void* module);
    bool (*is_compatible)(uint32_t protocol_version);
} module_interface_t;

/* Snapshot module interface */
typedef struct {
    module_interface_t base;
    
    /* Operations */
    void* (*create_snapshot)(validator_pos_t** validators, uint32_t count);
    void* (*update_incremental)(void* prev_snapshot, void* changes);
    bool (*verify_proof)(void* snapshot, const uint8_t* proof, size_t size);
    size_t (*get_proof_size)(void* snapshot);
} snapshot_module_t;

/* VRF module interface */
typedef struct {
    module_interface_t base;
    
    /* Operations */
    bool (*generate_keys)(uint8_t* public_out, uint8_t* private_out);
    void* (*compute_vrf)(const uint8_t* private_key, const uint8_t* message, size_t msg_len);
    bool (*verify_vrf)(const uint8_t* public_key, const uint8_t* message, size_t msg_len, void* vrf);
    bool (*is_aggregatable)(void);
    void* (*aggregate_vrfs)(void** vrfs, uint32_t count);  /* Optional */
} vrf_module_t;

/* Ordering module interface */
typedef struct {
    module_interface_t base;
    
    /* Operations */
    void* (*create_state)(narwhal_dag_t* dag, committee_t* committee);
    bool (*run_ordering)(void* state);
    uint32_t (*extract_transactions)(void* state, transaction_t** out, uint32_t max);
    consensus_mode_t (*select_mode)(void* state);
} ordering_module_t;

/* Proof module interface */
typedef struct {
    module_interface_t base;
    
    /* Operations */
    void* (*generate_proof)(const uint8_t* witness, size_t witness_size, void* config);
    bool (*verify_proof)(void* proof, void* config);
    bool (*supports_parallel)(void);
    void* (*combine_proofs)(void** proofs, uint32_t count);  /* For recursion */
} proof_module_t;

/* Parallel proof generation */
typedef struct {
    proof_module_t* proof_module;
    uint32_t num_workers;
    
    /* Parallel proofs */
    void* snapshot_proof;
    void* committee_proof;
    void* dag_proof;
    void* ordering_proof;
    
    /* Combined result */
    void* combined_proof;
    size_t combined_size;
} parallel_proof_gen_t;

/* Enhanced PoS state with modules */
typedef struct {
    /* Base state */
    pos_state_t base;
    
    /* Protocol version */
    uint32_t protocol_version;
    uint32_t min_protocol_version;
    
    /* Pluggable modules */
    snapshot_module_t* snapshot_module;
    vrf_module_t* vrf_module;
    ordering_module_t* ordering_module;
    proof_module_t* proof_module;
    
    /* Enhanced features */
    consensus_mode_t current_mode;
    bool fast_path_enabled;
    bool streaming_dag_enabled;
    bool parallel_proofs_enabled;
    
    /* Upgrade coordination */
    uint32_t upgrade_height;        /* When to switch versions */
    uint32_t next_protocol_version; /* Version to switch to */
    
    /* Module registry and upgrade state */
    module_interface_t** registered_modules;
    uint32_t registered_modules_count;
    upgrade_state_t* upgrade_state;
    pthread_rwlock_t module_lock;
} pos_state_v2_t;

/* Module registration */
bool cmptr_pos_register_snapshot_module(
    pos_state_v2_t* pos,
    snapshot_module_t* module,
    uint32_t version
);

bool cmptr_pos_register_vrf_module(
    pos_state_v2_t* pos,
    vrf_module_t* module,
    uint32_t version
);

bool cmptr_pos_register_ordering_module(
    pos_state_v2_t* pos,
    ordering_module_t* module,
    uint32_t version
);

bool cmptr_pos_register_proof_module(
    pos_state_v2_t* pos,
    proof_module_t* module,
    uint32_t version
);

/* Enhanced initialization */
pos_state_v2_t* cmptr_pos_v2_init(
    cmptr_accumulator_t* accumulator,
    blockchain_t* blockchain,
    uint32_t protocol_version
);

void cmptr_pos_v2_destroy(pos_state_v2_t* pos);

/* Parallel proof generation */
parallel_proof_gen_t* cmptr_pos_create_parallel_prover(
    proof_module_t* module,
    uint32_t num_workers
);

consensus_certificate_t* cmptr_pos_generate_parallel_certificate(
    pos_state_v2_t* pos,
    parallel_proof_gen_t* prover,
    const stake_snapshot_t* snapshot,
    const committee_t* committee,
    const mysticeti_state_t* ordering
);

/* Streaming DAG operations */
bool cmptr_pos_enable_streaming_dag(
    pos_state_v2_t* pos,
    uint32_t causality_threshold
);

bool cmptr_pos_process_streaming_vertex(
    pos_state_v2_t* pos,
    const narwhal_vertex_t* vertex
);

/* Fast path operations */
bool cmptr_pos_try_fast_path(
    pos_state_v2_t* pos,
    transaction_t** transactions,
    uint32_t tx_count
);

/* Incremental updates */
stake_snapshot_t* cmptr_pos_incremental_snapshot(
    pos_state_v2_t* pos,
    const stake_snapshot_t* previous,
    validator_pos_t** changed_validators,
    uint32_t change_count
);

/* Protocol upgrade coordination */
bool cmptr_pos_schedule_upgrade(
    pos_state_v2_t* pos,
    uint32_t target_height,
    uint32_t new_version
);

bool cmptr_pos_check_upgrade(
    pos_state_v2_t* pos,
    uint64_t current_height
);

/* Metrics for v2 */
typedef struct {
    pos_metrics_t base_metrics;
    
    /* Enhanced metrics */
    uint32_t fast_path_successes;
    uint32_t fast_path_attempts;
    double parallel_proof_speedup;
    uint32_t streaming_vertices_processed;
    uint64_t incremental_updates_saved;
    consensus_mode_t current_mode;
} pos_metrics_v2_t;

pos_metrics_v2_t cmptr_pos_v2_get_metrics(const pos_state_v2_t* pos);

/* Module registration and selection */
bool cmptr_pos_register_default_modules(pos_state_v2_t* pos);
bool cmptr_pos_select_modules_for_version(
    pos_state_v2_t* pos,
    uint32_t protocol_version
);

/* Demonstration functions */
void cmptr_pos_demonstrate_agility(pos_state_v2_t* pos);
void cmptr_pos_fast_path_demo(pos_state_v2_t* pos);
void cmptr_pos_streaming_dag_demo(pos_state_v2_t* pos);
void cmptr_pos_incremental_demo(pos_state_v2_t* pos);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_POS_V2_H */