/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef SEMANTIC_QA_H
#define SEMANTIC_QA_H

#include <stdint.h>
#include <stdbool.h>
#include <time.h>

// Hardware specification structure
typedef struct {
    char cpu_model[256];
    int cpu_cores;
    int cpu_threads;
    uint64_t cpu_freq_mhz;
    uint64_t ram_total_mb;
    uint64_t ram_available_mb;
    char os_name[128];
    char os_version[128];
    char compiler[128];
    char compiler_version[64];
    char architecture[64];
    bool has_avx2;
    bool has_avx512;
    char timestamp[64];
} hardware_spec_t;

// Benchmark result structure
typedef struct {
    char question[512];
    char answer[1024];
    double measurement_value;
    char measurement_unit[32];
    hardware_spec_t hardware;
    time_t timestamp;
    char test_function[128];
    bool success;
    char error_message[256];
    char additional_info[1024];
} benchmark_result_t;

// Question types
typedef enum {
    QA_TYPE_PERFORMANCE,
    QA_TYPE_CAPABILITY,
    QA_TYPE_COMPARISON,
    QA_TYPE_RESOURCE_USAGE,
    QA_TYPE_SCALABILITY
} qa_type_t;

// Question structure
typedef struct {
    const char* question;
    qa_type_t type;
    const char* test_function_name;
    const char* unit;
    const char* description;
} semantic_question_t;

// Function pointer for benchmark tests
typedef benchmark_result_t (*benchmark_test_fn)(void);

// Test registration structure
typedef struct {
    const char* name;
    benchmark_test_fn function;
    const char* description;
} benchmark_test_t;

// Core API functions

// Initialize the semantic Q&A system
int semantic_qa_init(const char* results_db_path);

// Detect current hardware specifications
void detect_hardware_specs(hardware_spec_t* spec);

// Register a benchmark test
int register_benchmark_test(const char* name, benchmark_test_fn fn, const char* description);

// Answer a question by running the appropriate test
benchmark_result_t answer_question(const char* question);

// Save benchmark result to database
int save_benchmark_result(const benchmark_result_t* result);

// Query historical results
int query_results(const char* question, benchmark_result_t* results, int max_results);

// Compare results across different hardware
int compare_hardware_performance(const char* question, benchmark_result_t* results, int max_results);

// Shutdown and cleanup
void semantic_qa_cleanup(void);

// Predefined questions
extern const semantic_question_t PREDEFINED_QUESTIONS[];
extern const int NUM_PREDEFINED_QUESTIONS;

#endif // SEMANTIC_QA_H