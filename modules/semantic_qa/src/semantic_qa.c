/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#define _GNU_SOURCE  // For strcasestr
#include "semantic_qa.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/utsname.h>
#include <sys/sysinfo.h>

// Maximum number of registered benchmark tests
#define MAX_BENCHMARK_TESTS 100

// Global state
static struct {
    char db_path[256];
    benchmark_test_t tests[MAX_BENCHMARK_TESTS];
    int num_tests;
    bool initialized;
} g_qa_state = {0};

// Predefined questions that the system can answer
const semantic_question_t PREDEFINED_QUESTIONS[] = {
    {
        "How long does this library take to prove a bitcoin block?",
        QA_TYPE_PERFORMANCE,
        "benchmark_bitcoin_proof_time",
        "seconds",
        "Measures time to generate a zero-knowledge proof for a 690K gate Bitcoin block verification circuit"
    },
    {
        "What is the gate evaluation throughput?",
        QA_TYPE_PERFORMANCE,
        "benchmark_gate_throughput",
        "gates/second",
        "Measures how many gates can be evaluated per second"
    },
    {
        "How much memory does a Bitcoin proof require?",
        QA_TYPE_RESOURCE_USAGE,
        "benchmark_bitcoin_proof_memory",
        "MB",
        "Measures peak memory usage during Bitcoin proof generation"
    },
    {
        "What is the proof size for a Bitcoin block?",
        QA_TYPE_CAPABILITY,
        "benchmark_bitcoin_proof_size",
        "bytes",
        "Measures the size of the generated zero-knowledge proof"
    },
    {
        "How long does SHA3-256 proof generation take?",
        QA_TYPE_PERFORMANCE,
        "benchmark_sha3_proof_time",
        "seconds",
        "Measures time to generate a proof for SHA3-256"
    },
    {
        "Can the system handle circuits with 1 million gates?",
        QA_TYPE_CAPABILITY,
        "test_million_gate_circuit",
        "boolean",
        "Tests whether the system can process very large circuits"
    },
    {
        "What is the verification time for a Bitcoin proof?",
        QA_TYPE_PERFORMANCE,
        "benchmark_bitcoin_verify_time",
        "seconds",
        "Measures time to verify a zero-knowledge proof"
    },
    {
        "How does performance scale with circuit size?",
        QA_TYPE_SCALABILITY,
        "benchmark_scaling_analysis",
        "gates/second",
        "Analyzes performance across different circuit sizes"
    }
};

const int NUM_PREDEFINED_QUESTIONS = sizeof(PREDEFINED_QUESTIONS) / sizeof(PREDEFINED_QUESTIONS[0]);

// Detect CPU features
static void detect_cpu_features(hardware_spec_t* spec) {
    // Check for AVX2 and AVX512
    spec->has_avx2 = false;
    spec->has_avx512 = false;
    
#ifdef __x86_64__
    FILE* cpuinfo = fopen("/proc/cpuinfo", "r");
    if (cpuinfo) {
        char line[256];
        while (fgets(line, sizeof(line), cpuinfo)) {
            if (strstr(line, "flags") || strstr(line, "Features")) {
                if (strstr(line, "avx2")) spec->has_avx2 = true;
                if (strstr(line, "avx512")) spec->has_avx512 = true;
                break;
            }
        }
        fclose(cpuinfo);
    }
#endif
}

// Get CPU model name
static void get_cpu_model(char* model, size_t size) {
    FILE* cpuinfo = fopen("/proc/cpuinfo", "r");
    if (cpuinfo) {
        char line[256];
        while (fgets(line, sizeof(line), cpuinfo)) {
            if (strstr(line, "model name")) {
                char* colon = strchr(line, ':');
                if (colon) {
                    strncpy(model, colon + 2, size - 1);
                    model[size - 1] = '\0';
                    // Remove newline
                    char* newline = strchr(model, '\n');
                    if (newline) *newline = '\0';
                    break;
                }
            }
        }
        fclose(cpuinfo);
    } else {
        strncpy(model, "Unknown CPU", size);
    }
}

// Detect hardware specifications
void detect_hardware_specs(hardware_spec_t* spec) {
    memset(spec, 0, sizeof(hardware_spec_t));
    
    // CPU information
    get_cpu_model(spec->cpu_model, sizeof(spec->cpu_model));
    spec->cpu_cores = sysconf(_SC_NPROCESSORS_CONF);
    spec->cpu_threads = sysconf(_SC_NPROCESSORS_ONLN);
    
    // Try to get CPU frequency
    FILE* freq_file = fopen("/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq", "r");
    if (freq_file) {
        uint64_t freq_khz;
        if (fscanf(freq_file, "%lu", &freq_khz) == 1) {
            spec->cpu_freq_mhz = freq_khz / 1000;
        }
        fclose(freq_file);
    }
    
    // Memory information
    struct sysinfo si;
    if (sysinfo(&si) == 0) {
        spec->ram_total_mb = si.totalram / (1024 * 1024);
        spec->ram_available_mb = si.freeram / (1024 * 1024);
    }
    
    // OS information
    struct utsname un;
    if (uname(&un) == 0) {
        strncpy(spec->os_name, un.sysname, sizeof(spec->os_name) - 1);
        strncpy(spec->os_version, un.release, sizeof(spec->os_version) - 1);
        strncpy(spec->architecture, un.machine, sizeof(spec->architecture) - 1);
    }
    
    // Compiler information
#ifdef __clang__
    snprintf(spec->compiler, sizeof(spec->compiler), "clang");
    snprintf(spec->compiler_version, sizeof(spec->compiler_version), "%d.%d.%d", 
             __clang_major__, __clang_minor__, __clang_patchlevel__);
#elif defined(__GNUC__)
    snprintf(spec->compiler, sizeof(spec->compiler), "gcc");
    snprintf(spec->compiler_version, sizeof(spec->compiler_version), "%d.%d.%d",
             __GNUC__, __GNUC_MINOR__, __GNUC_PATCHLEVEL__);
#else
    strncpy(spec->compiler, "unknown", sizeof(spec->compiler));
    strncpy(spec->compiler_version, "unknown", sizeof(spec->compiler_version));
#endif
    
    // CPU features
    detect_cpu_features(spec);
    
    // Timestamp
    time_t now = time(NULL);
    struct tm* tm = localtime(&now);
    strftime(spec->timestamp, sizeof(spec->timestamp), "%Y-%m-%d %H:%M:%S", tm);
}

// Initialize the semantic Q&A system
int semantic_qa_init(const char* results_db_path) {
    if (g_qa_state.initialized) {
        return 0;
    }
    
    if (results_db_path) {
        strncpy(g_qa_state.db_path, results_db_path, sizeof(g_qa_state.db_path) - 1);
    } else {
        strncpy(g_qa_state.db_path, "benchmark_results.db", sizeof(g_qa_state.db_path) - 1);
    }
    
    g_qa_state.num_tests = 0;
    g_qa_state.initialized = true;
    
    return 0;
}

// Register a benchmark test
int register_benchmark_test(const char* name, benchmark_test_fn fn, const char* description) {
    if (!g_qa_state.initialized) {
        return -1;
    }
    
    if (g_qa_state.num_tests >= MAX_BENCHMARK_TESTS) {
        return -1;
    }
    
    g_qa_state.tests[g_qa_state.num_tests].name = name;
    g_qa_state.tests[g_qa_state.num_tests].function = fn;
    g_qa_state.tests[g_qa_state.num_tests].description = description;
    g_qa_state.num_tests++;
    
    return 0;
}

// Find the best matching question
static const semantic_question_t* find_matching_question(const char* question) {
    // Simple keyword matching for now
    for (int i = 0; i < NUM_PREDEFINED_QUESTIONS; i++) {
        // Case-insensitive substring search
        if (strcasestr(question, "bitcoin") && strcasestr(question, "prove") && 
            strcasestr(PREDEFINED_QUESTIONS[i].question, "bitcoin") &&
            strcasestr(PREDEFINED_QUESTIONS[i].question, "prove")) {
            return &PREDEFINED_QUESTIONS[i];
        }
        
        if (strcasestr(question, "gate") && strcasestr(question, "throughput") &&
            strcasestr(PREDEFINED_QUESTIONS[i].question, "throughput")) {
            return &PREDEFINED_QUESTIONS[i];
        }
        
        if (strcasestr(question, "memory") && strcasestr(question, "proof") &&
            strcasestr(PREDEFINED_QUESTIONS[i].question, "memory")) {
            return &PREDEFINED_QUESTIONS[i];
        }
        
        // Add more matching logic as needed
    }
    
    return NULL;
}

// Find a registered test by name
static benchmark_test_fn find_test_by_name(const char* name) {
    for (int i = 0; i < g_qa_state.num_tests; i++) {
        if (strcmp(g_qa_state.tests[i].name, name) == 0) {
            return g_qa_state.tests[i].function;
        }
    }
    return NULL;
}

// Answer a question by running the appropriate test
benchmark_result_t answer_question(const char* question) {
    benchmark_result_t result = {0};
    strncpy(result.question, question, sizeof(result.question) - 1);
    result.timestamp = time(NULL);
    detect_hardware_specs(&result.hardware);
    
    // Find matching question
    const semantic_question_t* matched_q = find_matching_question(question);
    if (!matched_q) {
        result.success = false;
        snprintf(result.error_message, sizeof(result.error_message),
                 "No matching test found for question: %s", question);
        snprintf(result.answer, sizeof(result.answer),
                 "I don't know how to answer that question yet.");
        return result;
    }
    
    // Find and run the test
    benchmark_test_fn test_fn = find_test_by_name(matched_q->test_function_name);
    if (!test_fn) {
        result.success = false;
        snprintf(result.error_message, sizeof(result.error_message),
                 "Test function '%s' not registered", matched_q->test_function_name);
        snprintf(result.answer, sizeof(result.answer),
                 "The test for this question hasn't been implemented yet.");
        return result;
    }
    
    // Run the test
    strncpy(result.test_function, matched_q->test_function_name, sizeof(result.test_function) - 1);
    result = test_fn();
    
    // Ensure question is preserved
    strncpy(result.question, question, sizeof(result.question) - 1);
    
    return result;
}

// Save benchmark result to database (simple JSON format for now)
int save_benchmark_result(const benchmark_result_t* result) {
    FILE* f = fopen(g_qa_state.db_path, "a");
    if (!f) {
        return -1;
    }
    
    fprintf(f, "{\n");
    fprintf(f, "  \"question\": \"%s\",\n", result->question);
    fprintf(f, "  \"answer\": \"%s\",\n", result->answer);
    fprintf(f, "  \"measurement_value\": %.6f,\n", result->measurement_value);
    fprintf(f, "  \"measurement_unit\": \"%s\",\n", result->measurement_unit);
    fprintf(f, "  \"timestamp\": %ld,\n", result->timestamp);
    fprintf(f, "  \"success\": %s,\n", result->success ? "true" : "false");
    fprintf(f, "  \"test_function\": \"%s\",\n", result->test_function);
    fprintf(f, "  \"hardware\": {\n");
    fprintf(f, "    \"cpu_model\": \"%s\",\n", result->hardware.cpu_model);
    fprintf(f, "    \"cpu_cores\": %d,\n", result->hardware.cpu_cores);
    fprintf(f, "    \"cpu_threads\": %d,\n", result->hardware.cpu_threads);
    fprintf(f, "    \"cpu_freq_mhz\": %lu,\n", result->hardware.cpu_freq_mhz);
    fprintf(f, "    \"ram_total_mb\": %lu,\n", result->hardware.ram_total_mb);
    fprintf(f, "    \"os_name\": \"%s\",\n", result->hardware.os_name);
    fprintf(f, "    \"os_version\": \"%s\",\n", result->hardware.os_version);
    fprintf(f, "    \"compiler\": \"%s %s\",\n", result->hardware.compiler, result->hardware.compiler_version);
    fprintf(f, "    \"architecture\": \"%s\",\n", result->hardware.architecture);
    fprintf(f, "    \"has_avx2\": %s,\n", result->hardware.has_avx2 ? "true" : "false");
    fprintf(f, "    \"has_avx512\": %s\n", result->hardware.has_avx512 ? "true" : "false");
    fprintf(f, "  }\n");
    fprintf(f, "},\n");
    
    fclose(f);
    return 0;
}

// Cleanup
void semantic_qa_cleanup(void) {
    g_qa_state.initialized = false;
}