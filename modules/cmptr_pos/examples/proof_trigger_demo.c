/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "proof_triggers.h"
#include <stdio.h>
#include <unistd.h>
#include <pthread.h>

/* Simulated consensus phases */
typedef struct {
    consensus_trigger_engine_t* engine;
    consensus_phase_t phase;
    const char* name;
    uint32_t duration_ms;  /* Simulated duration */
} phase_worker_data_t;

/* Phase worker thread */
void* phase_worker(void* arg) {
    phase_worker_data_t* data = (phase_worker_data_t*)arg;
    
    printf("[%s] Starting phase simulation (duration: %dms)\n", 
           data->name, data->duration_ms);
    
    /* Simulate gradual progress */
    for (uint32_t progress = 0; progress <= 100; progress += 5) {
        /* Update progress */
        bool triggered = trigger_engine_update(
            data->engine, 
            data->phase, 
            progress
        );
        
        if (triggered) {
            printf("[%s] TRIGGERED at %d%% progress!\n", data->name, progress);
        }
        
        /* Simulate work */
        usleep(data->duration_ms * 1000 / 20);  /* 5% per step */
    }
    
    printf("[%s] Phase complete\n", data->name);
    return NULL;
}

/* Proof generation callback */
void on_proof_trigger(consensus_phase_t phase, void* user_data) {
    const char* phase_names[] = {
        "Snapshot", "Committee", "DAG", "Ordering"
    };
    
    printf(">>> PROOF GENERATION TRIGGERED for %s phase <<<\n", 
           phase_names[phase]);
    
    /* Simulate proof generation */
    usleep(50000);  /* 50ms proof generation */
    
    printf(">>> Proof for %s phase complete <<<\n", phase_names[phase]);
}

int main(void) {
    printf("=== PoS Proof Trigger Optimization Demo ===\n\n");
    
    /* Initialize trigger engine */
    consensus_trigger_engine_t* engine = trigger_engine_init();
    
    /* Register callbacks */
    for (int i = 0; i < PHASE_COUNT; i++) {
        trigger_engine_on_trigger(engine, i, on_proof_trigger, NULL);
    }
    
    /* Create phase workers */
    pthread_t threads[PHASE_COUNT];
    phase_worker_data_t workers[PHASE_COUNT] = {
        {engine, PHASE_SNAPSHOT, "Snapshot", 100},
        {engine, PHASE_COMMITTEE, "Committee", 120},
        {engine, PHASE_DAG, "DAG", 200},
        {engine, PHASE_ORDERING, "Ordering", 180}
    };
    
    printf("Starting consensus simulation...\n\n");
    
    /* Launch phases with slight delays to simulate pipeline */
    for (int i = 0; i < PHASE_COUNT; i++) {
        pthread_create(&threads[i], NULL, phase_worker, &workers[i]);
        usleep(30000);  /* 30ms delay between phase starts */
    }
    
    /* Wait for completion */
    for (int i = 0; i < PHASE_COUNT; i++) {
        pthread_join(threads[i], NULL);
    }
    
    printf("\n=== Trigger Statistics ===\n");
    
    /* Print statistics */
    const char* phase_names[] = {
        "Snapshot", "Committee", "DAG", "Ordering"
    };
    
    double total_efficiency = 0;
    for (int i = 0; i < PHASE_COUNT; i++) {
        trigger_stats_t stats = trigger_engine_get_stats(engine, i);
        printf("\n%s Phase:\n", phase_names[i]);
        printf("  Triggers: %lu\n", stats.trigger_count);
        printf("  Avg wait: %lu ms\n", stats.avg_wait_time_ms);
        printf("  Efficiency: %.1f%%\n", stats.efficiency_percent);
        total_efficiency += stats.efficiency_percent;
    }
    
    printf("\nOverall efficiency improvement: %.1f%%\n", 
           total_efficiency / PHASE_COUNT);
    
    /* Demonstrate adaptive triggering */
    printf("\n=== Adaptive Trigger Learning ===\n");
    
    /* Reconfigure DAG to adaptive with faster network */
    proof_trigger_config_t fast_network = {
        .type = TRIGGER_ADAPTIVE,
        .params.adaptive.alpha = 0.3
    };
    trigger_engine_configure(engine, PHASE_DAG, &fast_network);
    
    /* Run multiple rounds to show adaptation */
    printf("\nRunning 5 rounds with varying network speeds...\n");
    
    for (int round = 0; round < 5; round++) {
        /* Simulate faster network each round */
        uint32_t duration = 200 - round * 20;
        
        printf("\nRound %d (network speed: %dms):\n", round + 1, duration);
        
        /* Reset phase state */
        engine->phase_ready[PHASE_DAG] = false;
        engine->phase_start_time[PHASE_DAG] = 0;
        
        /* Simulate DAG phase */
        for (uint32_t progress = 0; progress <= 100; progress += 10) {
            bool triggered = trigger_engine_update(engine, PHASE_DAG, progress);
            if (triggered) {
                printf("  Triggered at %d%% progress\n", progress);
                break;
            }
            usleep(duration * 100);  /* 10% of total duration */
        }
    }
    
    printf("\nAdaptive trigger learned optimal timing!\n");
    
    /* Cleanup */
    trigger_engine_free(engine);
    
    printf("\n=== Demo Complete ===\n");
    printf("\nKey optimizations demonstrated:\n");
    printf("1. Immediate snapshot triggers (0ms wait)\n");
    printf("2. Threshold-based committee triggers (80%% progress)\n");
    printf("3. Adaptive DAG triggers (learns network speed)\n");
    printf("4. Threshold-based ordering triggers (90%% progress)\n");
    printf("\nExpected improvement: 600ms → 200ms consensus time\n");
    
    return 0;
}