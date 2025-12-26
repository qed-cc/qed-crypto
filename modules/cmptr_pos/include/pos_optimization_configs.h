/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_OPTIMIZATION_CONFIGS_H
#define CMPTR_POS_OPTIMIZATION_CONFIGS_H

#include <stdint.h>
#include <stdbool.h>
#include "proof_triggers.h"

/* Trigger engine configuration */
typedef struct {
    proof_trigger_type_t default_strategy;
    double learning_rate;
    bool enable_parallel;
} trigger_config_t;

/* Streaming DAG configuration */
typedef struct {
    bool enable_streaming;
    bool enable_circular_recursion;
    uint32_t max_round_size;
    uint32_t proof_workers;
} dag_config_t;

/* Hierarchical VRF tree configuration */
typedef struct {
    uint32_t initial_validators;
    uint32_t branching_factor;
    bool enable_caching;
    uint32_t cache_size;
} vrf_tree_config_t;

/* Missing function declarations for trigger engine */
static inline bool trigger_engine_should_trigger(
    consensus_trigger_engine_t* engine,
    consensus_phase_t phase
) {
    if (!engine || phase >= PHASE_COUNT) return false;
    return engine->phase_ready[phase];
}

static inline consensus_trigger_engine_t* trigger_engine_create(trigger_config_t* config) {
    consensus_trigger_engine_t* engine = trigger_engine_init();
    if (!engine || !config) return engine;
    
    /* Configure based on config */
    for (int i = 0; i < PHASE_COUNT; i++) {
        proof_trigger_config_t trigger_cfg = {
            .type = config->default_strategy
        };
        
        if (config->default_strategy == TRIGGER_ADAPTIVE) {
            trigger_cfg.params.adaptive.alpha = config->learning_rate;
        }
        
        trigger_engine_configure(engine, i, &trigger_cfg);
    }
    
    return engine;
}

static inline void trigger_engine_destroy(consensus_trigger_engine_t* engine) {
    trigger_engine_free(engine);
}

/* Blockchain type stub - would be defined in cmptr_blockchain module */
typedef struct blockchain blockchain_t;

#endif /* CMPTR_POS_OPTIMIZATION_CONFIGS_H */