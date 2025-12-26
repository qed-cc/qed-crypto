/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file logger.c
 * @brief Implementation of structured logging framework
 */

#include "logger.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

#ifdef __linux__
#include <sys/syscall.h>
#endif

// ANSI color codes
#define COLOR_RESET   "\033[0m"
#define COLOR_RED     "\033[31m"
#define COLOR_YELLOW  "\033[33m"
#define COLOR_BLUE    "\033[34m"
#define COLOR_GRAY    "\033[90m"
#define COLOR_WHITE   "\033[37m"

// Global logger state
static struct {
    logger_config_t config;
    FILE *log_file;
    pthread_mutex_t mutex;
    bool initialized;
    size_t current_file_size;
} g_logger = {
    .config = {
        .min_level = LOG_INFO,
        .format = LOG_FORMAT_TEXT,
        .log_file = NULL,
        .max_file_size = 100 * 1024 * 1024,  // 100MB default
        .rotation_count = 10,
        .include_timestamp = true,
        .include_thread_id = false,
        .include_source_location = true,
        .use_color = true
    },
    .log_file = NULL,
    .mutex = PTHREAD_MUTEX_INITIALIZER,
    .initialized = false,
    .current_file_size = 0
};

// Log level names
static const char* level_names[] = {
    "TRACE", "DEBUG", "INFO", "WARN", "ERROR", "FATAL"
};

// Log level colors
static const char* level_colors[] = {
    COLOR_GRAY, COLOR_BLUE, COLOR_WHITE, COLOR_YELLOW, COLOR_RED, COLOR_RED
};

// Get current thread ID
static long get_thread_id(void) {
#ifdef __linux__
    return syscall(SYS_gettid);
#else
    return (long)pthread_self();
#endif
}

// Get current timestamp
static void get_timestamp(char *buffer, size_t size) {
    struct timespec ts;
    struct tm tm_info;
    
    clock_gettime(CLOCK_REALTIME, &ts);
    localtime_r(&ts.tv_sec, &tm_info);
    
    snprintf(buffer, size, "%04d-%02d-%02d %02d:%02d:%02d.%03ld",
             tm_info.tm_year + 1900, tm_info.tm_mon + 1, tm_info.tm_mday,
             tm_info.tm_hour, tm_info.tm_min, tm_info.tm_sec,
             ts.tv_nsec / 1000000);
}

// Initialize logger
bool logger_init(const logger_config_t *config) {
    pthread_mutex_lock(&g_logger.mutex);
    
    if (g_logger.initialized) {
        pthread_mutex_unlock(&g_logger.mutex);
        return false;
    }
    
    if (config) {
        g_logger.config = *config;
    }
    
    // Open log file if specified
    if (g_logger.config.log_file) {
        g_logger.log_file = fopen(g_logger.config.log_file, "a");
        if (!g_logger.log_file) {
            fprintf(stderr, "Failed to open log file: %s\n", g_logger.config.log_file);
            pthread_mutex_unlock(&g_logger.mutex);
            return false;
        }
        
        // Get current file size
        struct stat st;
        if (fstat(fileno(g_logger.log_file), &st) == 0) {
            g_logger.current_file_size = st.st_size;
        }
        
        // Disable color for file output
        g_logger.config.use_color = false;
    }
    
    g_logger.initialized = true;
    pthread_mutex_unlock(&g_logger.mutex);
    
    LOG_INFO("logger", "Logger initialized (level: %s, format: %s)",
             level_names[g_logger.config.min_level],
             g_logger.config.format == LOG_FORMAT_JSON ? "json" : 
             g_logger.config.format == LOG_FORMAT_COMPACT ? "compact" : "text");
    
    return true;
}

// Shutdown logger
void logger_shutdown(void) {
    pthread_mutex_lock(&g_logger.mutex);
    
    if (g_logger.log_file) {
        fclose(g_logger.log_file);
        g_logger.log_file = NULL;
    }
    
    g_logger.initialized = false;
    pthread_mutex_unlock(&g_logger.mutex);
}

// Set log level
void logger_set_level(log_level_t level) {
    if (level >= LOG_TRACE && level <= LOG_FATAL) {
        g_logger.config.min_level = level;
    }
}

// Get log level
log_level_t logger_get_level(void) {
    return g_logger.config.min_level;
}

// Rotate log files
void logger_rotate_files(void) {
    if (!g_logger.config.log_file || !g_logger.log_file) {
        return;
    }
    
    pthread_mutex_lock(&g_logger.mutex);
    
    // Close current file
    fclose(g_logger.log_file);
    
    // Rotate existing files
    char old_name[4096], new_name[4096];
    for (int i = g_logger.config.rotation_count - 1; i > 0; i--) {
        snprintf(old_name, sizeof(old_name), "%s.%d", g_logger.config.log_file, i);
        snprintf(new_name, sizeof(new_name), "%s.%d", g_logger.config.log_file, i + 1);
        rename(old_name, new_name);
    }
    
    // Move current to .1
    snprintf(new_name, sizeof(new_name), "%s.1", g_logger.config.log_file);
    rename(g_logger.config.log_file, new_name);
    
    // Open new file
    g_logger.log_file = fopen(g_logger.config.log_file, "a");
    g_logger.current_file_size = 0;
    
    pthread_mutex_unlock(&g_logger.mutex);
}

// Format log message in text format
static void format_text(FILE *out, log_level_t level, const char *component,
                       const char *file, int line, const char *func,
                       const char *message) {
    char timestamp[64] = "";
    
    if (g_logger.config.include_timestamp) {
        get_timestamp(timestamp, sizeof(timestamp));
    }
    
    // Color for level
    if (g_logger.config.use_color && isatty(fileno(out))) {
        fprintf(out, "%s", level_colors[level]);
    }
    
    // Timestamp
    if (g_logger.config.include_timestamp) {
        fprintf(out, "%s ", timestamp);
    }
    
    // Level
    fprintf(out, "[%-5s] ", level_names[level]);
    
    // Component
    fprintf(out, "[%-12s] ", component);
    
    // Thread ID
    if (g_logger.config.include_thread_id) {
        fprintf(out, "[%5ld] ", get_thread_id());
    }
    
    // Message
    fprintf(out, "%s", message);
    
    // Source location
    if (g_logger.config.include_source_location && level >= LOG_DEBUG) {
        fprintf(out, " (%s:%d in %s)", file, line, func);
    }
    
    // Reset color
    if (g_logger.config.use_color && isatty(fileno(out))) {
        fprintf(out, "%s", COLOR_RESET);
    }
    
    fprintf(out, "\n");
}

// Format log message in JSON format
static void format_json(FILE *out, log_level_t level, const char *component,
                       const char *file, int line, const char *func,
                       const char *message) {
    char timestamp[64];
    get_timestamp(timestamp, sizeof(timestamp));
    
    fprintf(out, "{\"timestamp\":\"%s\",\"level\":\"%s\",\"component\":\"%s\"",
            timestamp, level_names[level], component);
    
    if (g_logger.config.include_thread_id) {
        fprintf(out, ",\"thread_id\":%ld", get_thread_id());
    }
    
    // Escape message for JSON
    fprintf(out, ",\"message\":\"");
    for (const char *p = message; *p; p++) {
        switch (*p) {
            case '"':  fprintf(out, "\\\""); break;
            case '\\': fprintf(out, "\\\\"); break;
            case '\b': fprintf(out, "\\b"); break;
            case '\f': fprintf(out, "\\f"); break;
            case '\n': fprintf(out, "\\n"); break;
            case '\r': fprintf(out, "\\r"); break;
            case '\t': fprintf(out, "\\t"); break;
            default:
                if (*p >= 32 && *p <= 126) {
                    fputc(*p, out);
                } else {
                    fprintf(out, "\\u%04x", (unsigned char)*p);
                }
        }
    }
    fprintf(out, "\"");
    
    if (g_logger.config.include_source_location) {
        fprintf(out, ",\"file\":\"%s\",\"line\":%d,\"function\":\"%s\"",
                file, line, func);
    }
    
    fprintf(out, "}\n");
}

// Format log message in compact format
static void format_compact(FILE *out, log_level_t level, const char *component,
                          const char *file, int line, const char *func,
                          const char *message) {
    (void)file;
    (void)line;
    (void)func;
    
    fprintf(out, "%c %s: %s\n",
            "TDIWEF"[level],  // Single character for level
            component,
            message);
}

// Core logging function
void log_write(log_level_t level, const char *component, 
               const char *file, int line, const char *func,
               const char *fmt, ...) {
    if (level < g_logger.config.min_level) {
        return;
    }
    
    // Format the message
    char message[4096];
    va_list args;
    va_start(args, fmt);
    vsnprintf(message, sizeof(message), fmt, args);
    va_end(args);
    
    pthread_mutex_lock(&g_logger.mutex);
    
    FILE *out = g_logger.log_file ? g_logger.log_file : stderr;
    
    // Check if rotation is needed
    if (g_logger.log_file && g_logger.current_file_size > g_logger.config.max_file_size) {
        pthread_mutex_unlock(&g_logger.mutex);
        logger_rotate_files();
        pthread_mutex_lock(&g_logger.mutex);
        out = g_logger.log_file ? g_logger.log_file : stderr;
    }
    
    // Format based on configuration
    switch (g_logger.config.format) {
        case LOG_FORMAT_JSON:
            format_json(out, level, component, file, line, func, message);
            break;
        case LOG_FORMAT_COMPACT:
            format_compact(out, level, component, file, line, func, message);
            break;
        default:
            format_text(out, level, component, file, line, func, message);
    }
    
    fflush(out);
    
    // Update file size estimate
    if (g_logger.log_file) {
        g_logger.current_file_size += strlen(message) + 100;  // Rough estimate
    }
    
    pthread_mutex_unlock(&g_logger.mutex);
}

// Log performance metrics
void log_performance(const char *component, const log_perf_metrics_t *metrics) {
    if (!metrics) return;
    
    char details[1024];
    int offset = 0;
    
    offset += snprintf(details + offset, sizeof(details) - offset,
                      "operation=%s duration_ms=%.2f",
                      metrics->operation, metrics->duration_ms);
    
    if (metrics->bytes_processed > 0) {
        offset += snprintf(details + offset, sizeof(details) - offset,
                          " bytes=%zu", metrics->bytes_processed);
    }
    
    if (metrics->throughput_mbps > 0) {
        offset += snprintf(details + offset, sizeof(details) - offset,
                          " throughput_mbps=%.2f", metrics->throughput_mbps);
    }
    
    if (metrics->gates_processed > 0) {
        offset += snprintf(details + offset, sizeof(details) - offset,
                          " gates=%lu", metrics->gates_processed);
    }
    
    if (metrics->gates_per_second > 0) {
        offset += snprintf(details + offset, sizeof(details) - offset,
                          " gates_per_second=%.2f", metrics->gates_per_second);
    }
    
    LOG_INFO(component, "Performance: %s", details);
}

// Log security event
void log_security_event(security_event_type_t event_type, 
                       const char *details, const char *source_ip) {
    const char *event_names[] = {
        "INVALID_INPUT", "PATH_TRAVERSAL", "OVERFLOW_ATTEMPT",
        "FORBIDDEN_ACCESS", "VALIDATION_FAILURE", "CRYPTO_ERROR"
    };
    
    const char *event_name = "UNKNOWN";
    if (event_type >= 0 && event_type < sizeof(event_names)/sizeof(event_names[0])) {
        event_name = event_names[event_type];
    }
    
    if (source_ip) {
        LOG_WARN("security", "Security event: type=%s source=%s details=%s",
                 event_name, source_ip, details);
    } else {
        LOG_WARN("security", "Security event: type=%s details=%s",
                 event_name, details);
    }
}

// Get log level name
const char* log_level_name(log_level_t level) {
    if (level >= LOG_TRACE && level <= LOG_FATAL) {
        return level_names[level];
    }
    return "UNKNOWN";
}

// Parse log level from string
bool log_level_from_string(const char *name, log_level_t *level) {
    if (!name || !level) return false;
    
    for (int i = 0; i <= LOG_FATAL; i++) {
        if (strcasecmp(name, level_names[i]) == 0) {
            *level = (log_level_t)i;
            return true;
        }
    }
    
    return false;
}