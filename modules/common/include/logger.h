/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef LOGGER_H
#define LOGGER_H

/**
 * @file logger.h
 * @brief Structured logging framework for Gate Computer
 * 
 * Provides structured logging with automatic context, log levels,
 * and output formatting suitable for production environments.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdarg.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Log levels
 */
typedef enum {
    LOG_TRACE = 0,    /**< Detailed trace information */
    LOG_DEBUG = 1,    /**< Debug information */
    LOG_INFO = 2,     /**< Informational messages */
    LOG_WARN = 3,     /**< Warning messages */
    LOG_ERROR = 4,    /**< Error messages */
    LOG_FATAL = 5     /**< Fatal error messages */
} log_level_t;

/**
 * @brief Log output format
 */
typedef enum {
    LOG_FORMAT_TEXT,      /**< Human-readable text format */
    LOG_FORMAT_JSON,      /**< JSON format for parsing */
    LOG_FORMAT_COMPACT    /**< Compact format for CLI */
} log_format_t;

/**
 * @brief Logger configuration
 */
typedef struct {
    log_level_t min_level;           /**< Minimum level to log */
    log_format_t format;             /**< Output format */
    const char *log_file;            /**< Log file path (NULL for stderr) */
    size_t max_file_size;            /**< Max log file size before rotation */
    int rotation_count;              /**< Number of rotated files to keep */
    bool include_timestamp;          /**< Include timestamp in logs */
    bool include_thread_id;          /**< Include thread ID in logs */
    bool include_source_location;    /**< Include file:line in logs */
    bool use_color;                  /**< Use ANSI colors (text format only) */
} logger_config_t;

/**
 * @brief Performance metrics for logging
 */
typedef struct {
    const char *operation;           /**< Operation name */
    double duration_ms;              /**< Duration in milliseconds */
    size_t bytes_processed;          /**< Bytes processed (optional) */
    double throughput_mbps;          /**< Throughput in MB/s (optional) */
    uint64_t gates_processed;        /**< Gates processed (optional) */
    double gates_per_second;         /**< Gates per second (optional) */
} log_perf_metrics_t;

/**
 * @brief Security event types
 */
typedef enum {
    SEC_EVENT_INVALID_INPUT,         /**< Invalid input detected */
    SEC_EVENT_PATH_TRAVERSAL,        /**< Path traversal attempt */
    SEC_EVENT_OVERFLOW_ATTEMPT,      /**< Buffer/integer overflow attempt */
    SEC_EVENT_FORBIDDEN_ACCESS,      /**< Access to forbidden resource */
    SEC_EVENT_VALIDATION_FAILURE,    /**< Input validation failure */
    SEC_EVENT_CRYPTO_ERROR          /**< Cryptographic operation error */
} security_event_type_t;

/**
 * @brief Initialize logger with configuration
 * 
 * @param config Logger configuration
 * @return true on success, false on failure
 */
bool logger_init(const logger_config_t *config);

/**
 * @brief Shutdown logger and free resources
 */
void logger_shutdown(void);

/**
 * @brief Set minimum log level
 * 
 * @param level Minimum level to log
 */
void logger_set_level(log_level_t level);

/**
 * @brief Get current log level
 * 
 * @return Current minimum log level
 */
log_level_t logger_get_level(void);

/**
 * @brief Core logging function
 * 
 * @param level Log level
 * @param component Component name
 * @param file Source file name
 * @param line Source line number
 * @param func Function name
 * @param fmt Format string
 * @param ... Format arguments
 */
void log_write(log_level_t level, const char *component, 
               const char *file, int line, const char *func,
               const char *fmt, ...) __attribute__((format(printf, 6, 7)));

/**
 * @brief Log with key-value pairs (for structured logging)
 * 
 * @param level Log level
 * @param component Component name
 * @param message Log message
 * @param ... Key-value pairs (terminated with NULL)
 */
void log_structured(log_level_t level, const char *component,
                   const char *message, ...);

/**
 * @brief Log performance metrics
 * 
 * @param component Component name
 * @param metrics Performance metrics
 */
void log_performance(const char *component, const log_perf_metrics_t *metrics);

/**
 * @brief Log security event
 * 
 * @param event_type Type of security event
 * @param details Event details
 * @param source_ip Source IP address (optional)
 */
void log_security_event(security_event_type_t event_type, 
                       const char *details, const char *source_ip);

/**
 * @brief Convenience macros for logging
 */
#define LOG_TRACE(component, fmt, ...) \
    log_write(LOG_TRACE, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

#define LOG_DEBUG(component, fmt, ...) \
    log_write(LOG_DEBUG, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

#define LOG_INFO(component, fmt, ...) \
    log_write(LOG_INFO, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

#define LOG_WARN(component, fmt, ...) \
    log_write(LOG_WARN, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

#define LOG_ERROR(component, fmt, ...) \
    log_write(LOG_ERROR, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

#define LOG_FATAL(component, fmt, ...) \
    log_write(LOG_FATAL, component, __FILE__, __LINE__, __func__, fmt, ##__VA_ARGS__)

/**
 * @brief Log entry/exit for function tracing
 */
#define LOG_ENTER() LOG_TRACE("trace", "Entering %s", __func__)
#define LOG_EXIT()  LOG_TRACE("trace", "Exiting %s", __func__)
#define LOG_RETURN(val) do { \
    LOG_TRACE("trace", "Exiting %s with value: %d", __func__, (int)(val)); \
    return (val); \
} while(0)

/**
 * @brief Get log level name as string
 * 
 * @param level Log level
 * @return String representation
 */
const char* log_level_name(log_level_t level);

/**
 * @brief Parse log level from string
 * 
 * @param name Level name (e.g., "INFO", "DEBUG")
 * @param level Output level
 * @return true if parsed successfully
 */
bool log_level_from_string(const char *name, log_level_t *level);

/**
 * @brief Rotate log files if needed
 * 
 * Called automatically when file size limit is reached
 */
void logger_rotate_files(void);

#ifdef __cplusplus
}
#endif

#endif // LOGGER_H