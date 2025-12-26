/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * semantic_qa_simple.c - Simple Q&A system for gate_computer benchmarks
 * 
 * This tool can answer questions about the library's performance by running
 * actual benchmarks and recording results with hardware specifications.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Include the header first
#include "../modules/semantic_qa/include/semantic_qa.h"

// Then include the implementations directly
#include "../modules/semantic_qa/src/semantic_qa.c"
#include "../modules/semantic_qa/src/benchmark_tests.c"

// ANSI color codes
#define COLOR_RESET   "\033[0m"
#define COLOR_BOLD    "\033[1m"
#define COLOR_GREEN   "\033[0;32m"
#define COLOR_BLUE    "\033[0;34m"
#define COLOR_YELLOW  "\033[0;33m"
#define COLOR_RED     "\033[0;31m"
#define COLOR_CYAN    "\033[0;36m"

void print_result(const benchmark_result_t* result) {
    printf("\n" COLOR_BOLD "========== Benchmark Result ==========\n" COLOR_RESET);
    printf(COLOR_CYAN "Question: " COLOR_RESET "%s\n", result->question);
    
    if (result->success) {
        printf(COLOR_GREEN "✅ Answer: " COLOR_RESET "%s\n", result->answer);
        
        if (result->measurement_value > 0) {
            printf(COLOR_BLUE "📊 Measurement: " COLOR_RESET "%.6f %s\n", 
                   result->measurement_value, result->measurement_unit);
        }
        
        printf("\n" COLOR_YELLOW "🖥️  Hardware Specifications:\n" COLOR_RESET);
        printf("   CPU: %s\n", result->hardware.cpu_model);
        printf("   Cores: %d (physical) / %d (logical)\n", 
               result->hardware.cpu_cores, result->hardware.cpu_threads);
        printf("   Memory: %lu MB\n", result->hardware.ram_total_mb);
        printf("   OS: %s %s\n", result->hardware.os_name, result->hardware.os_version);
        printf("   Compiler: %s %s\n", result->hardware.compiler, result->hardware.compiler_version);
        printf("   Architecture: %s\n", result->hardware.architecture);
        printf("   SIMD: %s%s\n", 
               result->hardware.has_avx2 ? "AVX2 " : "",
               result->hardware.has_avx512 ? "AVX512" : "");
        printf("   Timestamp: %s\n", result->hardware.timestamp);
        
        if (strlen(result->additional_info) > 0) {
            printf("\n" COLOR_CYAN "ℹ️  Additional Information:\n" COLOR_RESET);
            printf("   %s\n", result->additional_info);
        }
    } else {
        printf(COLOR_RED "❌ Error: " COLOR_RESET "%s\n", result->answer);
        if (strlen(result->error_message) > 0) {
            printf(COLOR_RED "   Details: " COLOR_RESET "%s\n", result->error_message);
        }
    }
    
    printf(COLOR_BOLD "=====================================\n" COLOR_RESET);
}

int main(int argc, char* argv[]) {
    // Initialize the Q&A system
    printf(COLOR_BOLD COLOR_BLUE "🤖 Gate Computer Semantic Q&A System\n" COLOR_RESET);
    printf("Initializing benchmark system...\n");
    
    semantic_qa_init("benchmark_results.json");
    register_all_benchmarks();
    
    if (argc < 2) {
        printf("\nUsage: %s <question_number>\n", argv[0]);
        printf("\nAvailable questions:\n");
        for (int i = 0; i < NUM_PREDEFINED_QUESTIONS; i++) {
            printf("  %d. %s\n", i + 1, PREDEFINED_QUESTIONS[i].question);
        }
        printf("\nExample: %s 1\n", argv[0]);
        return 1;
    }
    
    int question_num = atoi(argv[1]);
    if (question_num < 1 || question_num > NUM_PREDEFINED_QUESTIONS) {
        printf(COLOR_RED "Error: Invalid question number. Choose 1-%d\n" COLOR_RESET, 
               NUM_PREDEFINED_QUESTIONS);
        return 1;
    }
    
    const char* question = PREDEFINED_QUESTIONS[question_num - 1].question;
    printf("\n" COLOR_YELLOW "⏳ Running benchmark for: " COLOR_RESET "%s\n", question);
    
    // Answer the question by running the benchmark
    benchmark_result_t result = answer_question(question);
    
    // Display the result
    print_result(&result);
    
    // Save to database
    if (result.success) {
        printf("\n💾 Saving result to benchmark database...\n");
        save_benchmark_result(&result);
        printf("✅ Result saved to benchmark_results.json\n");
    }
    
    // Cleanup
    semantic_qa_cleanup();
    
    return result.success ? 0 : 1;
}