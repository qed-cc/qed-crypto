/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "parallel_proof_pipeline.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>
#include <unistd.h>

/* Get current time in microseconds */
static uint64_t get_time_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000ULL + ts.tv_nsec / 1000;
}

/* Get number of CPU cores */
static uint32_t get_num_cores(void) {
    long cores = sysconf(_SC_NPROCESSORS_ONLN);
    return (cores > 0) ? (uint32_t)cores : 4;
}

/* Worker thread function */
static void* pipeline_worker_thread(void* arg) {
    pipeline_worker_t* worker = (pipeline_worker_t*)arg;
    pipeline_stage_t* stage = &((parallel_pipeline_t*)worker->context)->stages[worker->stage];
    
    while (true) {
        /* Get work from queue */
        pthread_mutex_lock(&worker->queue_lock);
        
        while (worker->tail == worker->head && !((parallel_pipeline_t*)worker->context)->shutdown) {
            uint64_t idle_start = get_time_us();
            pthread_cond_wait(&worker->work_available, &worker->queue_lock);
            worker->idle_time_us += get_time_us() - idle_start;
        }
        
        if (((parallel_pipeline_t*)worker->context)->shutdown && worker->tail == worker->head) {
            pthread_mutex_unlock(&worker->queue_lock);
            break;
        }
        
        /* Get work item */
        pipeline_work_t* work = worker->queue[worker->tail];
        worker->tail = (worker->tail + 1) % worker->queue_size;
        pthread_mutex_unlock(&worker->queue_lock);
        
        /* Process work */
        uint64_t start = get_time_us();
        
        bool success = stage->process(work, stage->context);
        
        uint64_t end = get_time_us();
        worker->total_time_us += (end - start);
        worker->items_processed++;
        
        if (success) {
            /* Pass to next stage or complete */
            if (stage->next_stage) {
                /* Find least loaded worker in next stage */
                pipeline_stage_t* next = stage->next_stage;
                uint32_t best_worker = 0;
                uint32_t min_load = UINT32_MAX;
                
                for (uint32_t i = 0; i < next->config.num_workers; i++) {
                    pthread_mutex_lock(&next->workers[i].queue_lock);
                    uint32_t load = (next->workers[i].head - next->workers[i].tail + 
                                    next->workers[i].queue_size) % next->workers[i].queue_size;
                    pthread_mutex_unlock(&next->workers[i].queue_lock);
                    
                    if (load < min_load) {
                        min_load = load;
                        best_worker = i;
                    }
                }
                
                /* Submit to next stage */
                pipeline_worker_t* next_worker = &next->workers[best_worker];
                pthread_mutex_lock(&next_worker->queue_lock);
                
                uint32_t next_head = (next_worker->head + 1) % next_worker->queue_size;
                if (next_head != next_worker->tail) {
                    next_worker->queue[next_worker->head] = work;
                    next_worker->head = next_head;
                    pthread_cond_signal(&next_worker->work_available);
                }
                
                pthread_mutex_unlock(&next_worker->queue_lock);
            } else {
                /* Final stage - call completion callback */
                work->complete_time = get_time_us();
                parallel_pipeline_t* pipeline = (parallel_pipeline_t*)worker->context;
                
                if (pipeline->on_complete) {
                    pipeline->on_complete(work, pipeline->user_data);
                }
                
                /* Update completion stats */
                __atomic_add_fetch(&pipeline->items_completed, 1, __ATOMIC_RELAXED);
            }
        } else {
            /* Handle failure - in production would have error callback */
            free(work->input_data);
            free(work->output_data);
            free(work);
        }
        
        /* Update stage statistics */
        pthread_mutex_lock(&stage->stats_lock);
        stage->total_items++;
        stage->total_latency_us += (end - start);
        pthread_mutex_unlock(&stage->stats_lock);
    }
    
    /* Cleanup on shutdown */
    pthread_mutex_lock(&((parallel_pipeline_t*)worker->context)->shutdown_lock);
    ((parallel_pipeline_t*)worker->context)->active_workers--;
    if (((parallel_pipeline_t*)worker->context)->active_workers == 0) {
        pthread_cond_signal(&((parallel_pipeline_t*)worker->context)->shutdown_complete);
    }
    pthread_mutex_unlock(&((parallel_pipeline_t*)worker->context)->shutdown_lock);
    
    return NULL;
}

/* Stage processing functions */
bool stage_witness_generation(pipeline_work_t* work, void* context) {
    /* Simulate witness generation */
    usleep(5000);  /* 5ms */
    
    /* Allocate output for next stage */
    work->output_size = 64 * 1024;  /* 64KB witness */
    work->output_data = malloc(work->output_size);
    memset(work->output_data, 0xAA, work->output_size);
    
    return true;
}

bool stage_polynomial_commit(pipeline_work_t* work, void* context) {
    /* Simulate polynomial commitment */
    usleep(8000);  /* 8ms */
    
    /* Transform witness to polynomial commitment */
    free(work->input_data);
    work->input_data = work->output_data;
    work->input_size = work->output_size;
    
    work->output_size = 32 * 1024;  /* 32KB commitment */
    work->output_data = malloc(work->output_size);
    memset(work->output_data, 0xBB, work->output_size);
    
    return true;
}

bool stage_sumcheck(pipeline_work_t* work, void* context) {
    /* Simulate sumcheck protocol */
    usleep(15000);  /* 15ms - most expensive stage */
    
    /* Generate sumcheck proof */
    free(work->input_data);
    work->input_data = work->output_data;
    work->input_size = work->output_size;
    
    work->output_size = 40 * 1024;  /* 40KB sumcheck proof */
    work->output_data = malloc(work->output_size);
    memset(work->output_data, 0xCC, work->output_size);
    
    return true;
}

bool stage_merkle_build(pipeline_work_t* work, void* context) {
    /* Simulate Merkle tree construction */
    usleep(6000);  /* 6ms */
    
    /* Build Merkle paths */
    free(work->input_data);
    work->input_data = work->output_data;
    work->input_size = work->output_size;
    
    work->output_size = 45 * 1024;  /* 45KB with paths */
    work->output_data = malloc(work->output_size);
    memset(work->output_data, 0xDD, work->output_size);
    
    return true;
}

bool stage_final_compose(pipeline_work_t* work, void* context) {
    /* Simulate final proof composition */
    usleep(4000);  /* 4ms */
    
    /* Compose final proof */
    free(work->input_data);
    work->input_data = work->output_data;
    work->input_size = work->output_size;
    
    work->output_size = 190 * 1024;  /* 190KB final proof */
    work->output_data = malloc(work->output_size);
    memset(work->output_data, 0xEE, work->output_size);
    
    /* In real implementation, would call basefold_raa_prove() here */
    
    return true;
}

/* Get optimal pipeline configuration */
stage_config_t* get_optimal_pipeline_config(uint32_t num_cores) {
    static stage_config_t configs[STAGE_COUNT];
    
    /* Distribute workers based on stage complexity */
    uint32_t total_workers = num_cores;
    
    configs[STAGE_WITNESS_GEN] = (stage_config_t){
        .stage = STAGE_WITNESS_GEN,
        .num_workers = 2,
        .queue_size = 32,
        .expected_time_ms = 5.0,
        .can_parallelize = true
    };
    
    configs[STAGE_POLYNOMIAL_COMMIT] = (stage_config_t){
        .stage = STAGE_POLYNOMIAL_COMMIT,
        .num_workers = 3,
        .queue_size = 32,
        .expected_time_ms = 8.0,
        .can_parallelize = true
    };
    
    configs[STAGE_SUMCHECK] = (stage_config_t){
        .stage = STAGE_SUMCHECK,
        .num_workers = 4,  /* Most workers for bottleneck stage */
        .queue_size = 64,
        .expected_time_ms = 15.0,
        .can_parallelize = true
    };
    
    configs[STAGE_MERKLE_BUILD] = (stage_config_t){
        .stage = STAGE_MERKLE_BUILD,
        .num_workers = 2,
        .queue_size = 32,
        .expected_time_ms = 6.0,
        .can_parallelize = true
    };
    
    configs[STAGE_FINAL_COMPOSE] = (stage_config_t){
        .stage = STAGE_FINAL_COMPOSE,
        .num_workers = 1,  /* Sequential final stage */
        .queue_size = 16,
        .expected_time_ms = 4.0,
        .can_parallelize = false
    };
    
    /* Adjust worker counts based on available cores */
    if (num_cores < 12) {
        /* Scale down for fewer cores */
        for (int i = 0; i < STAGE_COUNT; i++) {
            configs[i].num_workers = (configs[i].num_workers * num_cores) / 12;
            if (configs[i].num_workers == 0) configs[i].num_workers = 1;
        }
    }
    
    return configs;
}

/* Create pipeline */
parallel_pipeline_t* pipeline_create(stage_config_t* configs, uint32_t num_stages) {
    parallel_pipeline_t* pipeline = calloc(1, sizeof(parallel_pipeline_t));
    if (!pipeline) return NULL;
    
    pipeline->enabled = true;
    pipeline->start_time = get_time_us();
    
    /* Initialize stages */
    for (uint32_t s = 0; s < num_stages && s < STAGE_COUNT; s++) {
        pipeline_stage_t* stage = &pipeline->stages[s];
        stage->config = configs[s];
        
        /* Set processing function */
        switch (s) {
            case STAGE_WITNESS_GEN:
                stage->process = stage_witness_generation;
                break;
            case STAGE_POLYNOMIAL_COMMIT:
                stage->process = stage_polynomial_commit;
                break;
            case STAGE_SUMCHECK:
                stage->process = stage_sumcheck;
                break;
            case STAGE_MERKLE_BUILD:
                stage->process = stage_merkle_build;
                break;
            case STAGE_FINAL_COMPOSE:
                stage->process = stage_final_compose;
                break;
        }
        
        /* Link stages */
        if (s < num_stages - 1) {
            stage->next_stage = &pipeline->stages[s + 1];
        }
        
        /* Initialize workers */
        stage->workers = calloc(stage->config.num_workers, sizeof(pipeline_worker_t));
        pipeline->total_workers += stage->config.num_workers;
        
        for (uint32_t w = 0; w < stage->config.num_workers; w++) {
            pipeline_worker_t* worker = &stage->workers[w];
            worker->worker_id = w;
            worker->stage = s;
            worker->queue_size = stage->config.queue_size;
            worker->queue = calloc(worker->queue_size, sizeof(pipeline_work_t*));
            worker->context = pipeline;
            
            pthread_mutex_init(&worker->queue_lock, NULL);
            pthread_cond_init(&worker->work_available, NULL);
            
            /* Start worker thread */
            pthread_create(&worker->thread, NULL, pipeline_worker_thread, worker);
            pipeline->active_workers++;
        }
        
        pthread_mutex_init(&stage->stats_lock, NULL);
    }
    
    /* Initialize input queue */
    pipeline->input_queue_size = 128;
    pipeline->input_queue = calloc(pipeline->input_queue_size, sizeof(pipeline_work_t*));
    pthread_mutex_init(&pipeline->input_lock, NULL);
    pthread_cond_init(&pipeline->input_not_full, NULL);
    
    /* Initialize shutdown control */
    pthread_mutex_init(&pipeline->shutdown_lock, NULL);
    pthread_cond_init(&pipeline->shutdown_complete, NULL);
    
    return pipeline;
}

/* Destroy pipeline */
void pipeline_destroy(parallel_pipeline_t* pipeline) {
    if (!pipeline) return;
    
    /* Initiate shutdown */
    pthread_mutex_lock(&pipeline->shutdown_lock);
    pipeline->shutdown = true;
    pthread_mutex_unlock(&pipeline->shutdown_lock);
    
    /* Wake all workers */
    for (uint32_t s = 0; s < STAGE_COUNT; s++) {
        pipeline_stage_t* stage = &pipeline->stages[s];
        for (uint32_t w = 0; w < stage->config.num_workers; w++) {
            pthread_mutex_lock(&stage->workers[w].queue_lock);
            pthread_cond_signal(&stage->workers[w].work_available);
            pthread_mutex_unlock(&stage->workers[w].queue_lock);
        }
    }
    
    /* Wait for workers to finish */
    pthread_mutex_lock(&pipeline->shutdown_lock);
    while (pipeline->active_workers > 0) {
        pthread_cond_wait(&pipeline->shutdown_complete, &pipeline->shutdown_lock);
    }
    pthread_mutex_unlock(&pipeline->shutdown_lock);
    
    /* Join threads and cleanup */
    for (uint32_t s = 0; s < STAGE_COUNT; s++) {
        pipeline_stage_t* stage = &pipeline->stages[s];
        
        for (uint32_t w = 0; w < stage->config.num_workers; w++) {
            pthread_join(stage->workers[w].thread, NULL);
            pthread_mutex_destroy(&stage->workers[w].queue_lock);
            pthread_cond_destroy(&stage->workers[w].work_available);
            free(stage->workers[w].queue);
        }
        
        free(stage->workers);
        pthread_mutex_destroy(&stage->stats_lock);
    }
    
    /* Cleanup input queue */
    free(pipeline->input_queue);
    pthread_mutex_destroy(&pipeline->input_lock);
    pthread_cond_destroy(&pipeline->input_not_full);
    pthread_mutex_destroy(&pipeline->shutdown_lock);
    pthread_cond_destroy(&pipeline->shutdown_complete);
    
    free(pipeline);
}

/* Submit work to pipeline */
bool pipeline_submit(
    parallel_pipeline_t* pipeline,
    consensus_phase_t phase,
    void* witness_data,
    size_t witness_size
) {
    if (!pipeline || pipeline->shutdown) return false;
    
    /* Create work item */
    pipeline_work_t* work = calloc(1, sizeof(pipeline_work_t));
    work->id = __atomic_add_fetch(&pipeline->items_submitted, 1, __ATOMIC_RELAXED);
    work->phase = phase;
    work->input_data = malloc(witness_size);
    memcpy(work->input_data, witness_data, witness_size);
    work->input_size = witness_size;
    work->enqueue_time = get_time_us();
    
    /* Submit to first stage with least loaded worker */
    pipeline_stage_t* first_stage = &pipeline->stages[0];
    uint32_t best_worker = 0;
    uint32_t min_load = UINT32_MAX;
    
    for (uint32_t w = 0; w < first_stage->config.num_workers; w++) {
        pthread_mutex_lock(&first_stage->workers[w].queue_lock);
        uint32_t load = (first_stage->workers[w].head - first_stage->workers[w].tail + 
                        first_stage->workers[w].queue_size) % first_stage->workers[w].queue_size;
        pthread_mutex_unlock(&first_stage->workers[w].queue_lock);
        
        if (load < min_load) {
            min_load = load;
            best_worker = w;
        }
    }
    
    /* Enqueue work */
    pipeline_worker_t* worker = &first_stage->workers[best_worker];
    pthread_mutex_lock(&worker->queue_lock);
    
    uint32_t next_head = (worker->head + 1) % worker->queue_size;
    if (next_head == worker->tail) {
        /* Queue full */
        pthread_mutex_unlock(&worker->queue_lock);
        free(work->input_data);
        free(work);
        return false;
    }
    
    worker->queue[worker->head] = work;
    worker->head = next_head;
    pthread_cond_signal(&worker->work_available);
    pthread_mutex_unlock(&worker->queue_lock);
    
    return true;
}

/* Get pipeline statistics */
pipeline_stats_t pipeline_get_stats(parallel_pipeline_t* pipeline) {
    pipeline_stats_t stats = {0};
    
    if (!pipeline) return stats;
    
    uint64_t now = get_time_us();
    uint64_t runtime = now - pipeline->start_time;
    
    /* Per-stage statistics */
    for (uint32_t s = 0; s < STAGE_COUNT; s++) {
        pipeline_stage_t* stage = &pipeline->stages[s];
        
        uint64_t total_processed = 0;
        uint64_t total_time = 0;
        uint64_t total_idle = 0;
        uint32_t total_queued = 0;
        
        for (uint32_t w = 0; w < stage->config.num_workers; w++) {
            pipeline_worker_t* worker = &stage->workers[w];
            total_processed += worker->items_processed;
            total_time += worker->total_time_us;
            total_idle += worker->idle_time_us;
            
            pthread_mutex_lock(&worker->queue_lock);
            total_queued += (worker->head - worker->tail + worker->queue_size) % worker->queue_size;
            pthread_mutex_unlock(&worker->queue_lock);
        }
        
        stats.stages[s].items_processed = total_processed;
        stats.stages[s].queue_depth = total_queued;
        
        if (total_processed > 0) {
            stats.stages[s].avg_latency_ms = (double)total_time / total_processed / 1000.0;
        }
        
        uint64_t worker_runtime = runtime * stage->config.num_workers;
        if (worker_runtime > 0) {
            stats.stages[s].utilization_percent = 
                (double)(worker_runtime - total_idle) / worker_runtime * 100.0;
        }
    }
    
    /* Overall statistics */
    if (runtime > 0) {
        stats.total_throughput = (double)pipeline->items_completed * 1000000.0 / runtime;
    }
    
    if (pipeline->items_completed > 0) {
        /* Calculate average end-to-end latency */
        double total_stage_time = 0;
        for (uint32_t s = 0; s < STAGE_COUNT; s++) {
            total_stage_time += stats.stages[s].avg_latency_ms;
        }
        stats.end_to_end_latency_ms = total_stage_time;
        
        /* Calculate efficiency */
        double sequential_time = total_stage_time * pipeline->items_completed;
        double parallel_time = (double)runtime / 1000.0;
        stats.efficiency_percent = (sequential_time / parallel_time) / pipeline->total_workers * 100.0;
    }
    
    return stats;
}