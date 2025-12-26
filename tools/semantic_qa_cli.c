/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * semantic_qa_cli.c - Interactive Q&A system for gate_computer benchmarks
 * 
 * This tool can answer questions about the library's performance by running
 * actual benchmarks and recording results with hardware specifications.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <readline/readline.h>
#include <readline/history.h>

// Simplified version - include the implementations directly for now
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

void print_welcome(void) {
    printf("\n");
    printf(COLOR_BOLD COLOR_BLUE "🤖 Gate Computer Semantic Q&A System\n" COLOR_RESET);
    printf(COLOR_BOLD "====================================\n" COLOR_RESET);
    printf("\n");
    printf("I can answer questions about the gate_computer library's performance\n");
    printf("by running actual benchmarks on your hardware.\n");
    printf("\n");
    printf(COLOR_CYAN "Example questions:\n" COLOR_RESET);
    printf("  • How long does this library take to prove a bitcoin block?\n");
    printf("  • What is the gate evaluation throughput?\n");
    printf("  • How much memory does a Bitcoin proof require?\n");
    printf("  • Can the system handle circuits with 1 million gates?\n");
    printf("\n");
    printf("Type " COLOR_GREEN "'list'" COLOR_RESET " to see all questions, "
           COLOR_GREEN "'help'" COLOR_RESET " for commands, or "
           COLOR_GREEN "'quit'" COLOR_RESET " to exit.\n");
    printf("\n");
}

void print_hardware_info(const hardware_spec_t* hw) {
    printf(COLOR_BOLD "\n📊 Hardware Information:\n" COLOR_RESET);
    printf("   CPU: %s\n", hw->cpu_model);
    printf("   Cores/Threads: %d/%d\n", hw->cpu_cores, hw->cpu_threads);
    if (hw->cpu_freq_mhz > 0) {
        printf("   Frequency: %lu MHz\n", hw->cpu_freq_mhz);
    }
    printf("   Memory: %lu MB total, %lu MB available\n", hw->ram_total_mb, hw->ram_available_mb);
    printf("   OS: %s %s (%s)\n", hw->os_name, hw->os_version, hw->architecture);
    printf("   Compiler: %s %s\n", hw->compiler, hw->compiler_version);
    printf("   Features: %s%s\n", 
           hw->has_avx2 ? "AVX2 " : "",
           hw->has_avx512 ? "AVX512" : "");
    printf("\n");
}

void list_questions(void) {
    printf(COLOR_BOLD "\n📋 Available Questions:\n" COLOR_RESET);
    for (int i = 0; i < NUM_PREDEFINED_QUESTIONS; i++) {
        printf(COLOR_GREEN "%d. " COLOR_RESET "%s\n", i + 1, PREDEFINED_QUESTIONS[i].question);
        printf("   " COLOR_CYAN "→ %s\n" COLOR_RESET, PREDEFINED_QUESTIONS[i].description);
    }
    printf("\n");
}

void print_result(const benchmark_result_t* result) {
    if (result->success) {
        printf(COLOR_BOLD COLOR_GREEN "\n✅ Answer:\n" COLOR_RESET);
        printf("%s\n", result->answer);
        
        if (result->measurement_value > 0) {
            printf(COLOR_CYAN "\n📏 Measurement: " COLOR_RESET);
            printf("%.6f %s\n", result->measurement_value, result->measurement_unit);
        }
        
        if (strlen(result->additional_info) > 0) {
            printf(COLOR_YELLOW "\n💡 Additional Info:\n" COLOR_RESET);
            printf("%s\n", result->additional_info);
        }
    } else {
        printf(COLOR_BOLD COLOR_RED "\n❌ Error:\n" COLOR_RESET);
        printf("%s\n", result->answer);
        if (strlen(result->error_message) > 0) {
            printf(COLOR_RED "Details: %s\n" COLOR_RESET, result->error_message);
        }
    }
}

void show_help(void) {
    printf(COLOR_BOLD "\n📖 Commands:\n" COLOR_RESET);
    printf("  " COLOR_GREEN "list" COLOR_RESET "     - Show all available questions\n");
    printf("  " COLOR_GREEN "hardware" COLOR_RESET " - Show detailed hardware information\n");
    printf("  " COLOR_GREEN "history" COLOR_RESET "  - Show recent benchmark results\n");
    printf("  " COLOR_GREEN "compare" COLOR_RESET "  - Compare results across different hardware\n");
    printf("  " COLOR_GREEN "save" COLOR_RESET "     - Save current session results\n");
    printf("  " COLOR_GREEN "help" COLOR_RESET "     - Show this help message\n");
    printf("  " COLOR_GREEN "quit" COLOR_RESET "     - Exit the program\n");
    printf("\n");
    printf("You can also type a question number (1-%d) to run that benchmark.\n", NUM_PREDEFINED_QUESTIONS);
    printf("\n");
}

void show_recent_history(void) {
    printf(COLOR_BOLD "\n📜 Recent Benchmark Results:\n" COLOR_RESET);
    
    FILE* f = fopen("benchmark_results.db", "r");
    if (!f) {
        printf("No benchmark history found.\n");
        return;
    }
    
    // Simple display of last few results
    char line[1024];
    int count = 0;
    while (fgets(line, sizeof(line), f) && count < 5) {
        if (strstr(line, "\"question\"")) {
            printf("\n%s", line);
            count++;
        } else if (strstr(line, "\"answer\"") || strstr(line, "\"measurement_value\"")) {
            printf("%s", line);
        }
    }
    
    fclose(f);
    printf("\n");
}

int main(int argc, char* argv[]) {
    // Initialize the Q&A system
    semantic_qa_init("benchmark_results.db");
    register_all_benchmarks();
    
    // Show hardware info on startup
    hardware_spec_t hw;
    detect_hardware_specs(&hw);
    
    print_welcome();
    print_hardware_info(&hw);
    
    // Interactive loop
    char* input;
    while ((input = readline(COLOR_BOLD "> " COLOR_RESET)) != NULL) {
        if (strlen(input) == 0) {
            free(input);
            continue;
        }
        
        add_history(input);
        
        // Process commands
        if (strcasecmp(input, "quit") == 0 || strcasecmp(input, "exit") == 0) {
            free(input);
            break;
        } else if (strcasecmp(input, "list") == 0) {
            list_questions();
        } else if (strcasecmp(input, "help") == 0) {
            show_help();
        } else if (strcasecmp(input, "hardware") == 0) {
            print_hardware_info(&hw);
        } else if (strcasecmp(input, "history") == 0) {
            show_recent_history();
        } else {
            // Check if it's a number
            char* endptr;
            long num = strtol(input, &endptr, 10);
            if (*endptr == '\0' && num > 0 && num <= NUM_PREDEFINED_QUESTIONS) {
                // Run benchmark by number
                printf(COLOR_YELLOW "\n⏳ Running benchmark...\n" COLOR_RESET);
                benchmark_result_t result = answer_question(PREDEFINED_QUESTIONS[num - 1].question);
                print_result(&result);
                save_benchmark_result(&result);
            } else {
                // Try to answer as a natural language question
                printf(COLOR_YELLOW "\n⏳ Analyzing question and running benchmark...\n" COLOR_RESET);
                benchmark_result_t result = answer_question(input);
                print_result(&result);
                if (result.success) {
                    save_benchmark_result(&result);
                }
            }
        }
        
        free(input);
    }
    
    printf(COLOR_BOLD "\n👋 Goodbye!\n" COLOR_RESET);
    semantic_qa_cleanup();
    
    return 0;
}