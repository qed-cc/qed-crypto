/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_STREAMING_DAG_HELPERS_H
#define CMPTR_POS_STREAMING_DAG_HELPERS_H

#include "streaming_dag.h"
#include "pos_optimization_configs.h"

/* Create streaming DAG from config */
static inline streaming_dag_engine_t* streaming_dag_create(dag_config_t* config) {
    if (!config) return NULL;
    
    return streaming_dag_init(
        config->enable_streaming,
        config->proof_workers > 1
    );
}

/* Destroy streaming DAG */
static inline void streaming_dag_destroy(streaming_dag_engine_t* engine) {
    streaming_dag_free(engine);
}

/* Start a new round */
static inline void streaming_dag_start_round(streaming_dag_engine_t* engine, uint32_t round) {
    if (!engine) return;
    /* Round is started implicitly when vertices are added */
}

/* Finalize current round */
static inline void streaming_dag_finalize_round(streaming_dag_engine_t* engine, uint32_t round) {
    if (!engine) return;
    /* Complete the current round */
    streaming_dag_complete_round(engine);
}

#endif /* CMPTR_POS_STREAMING_DAG_HELPERS_H */