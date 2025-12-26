/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef INPUT_VALIDATION_H
#define INPUT_VALIDATION_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/**
 * @file input_validation.h
 * @brief Comprehensive input validation functions for security
 * 
 * This module provides secure input validation functions to prevent:
 * - Buffer overflows
 * - Integer overflows
 * - Path traversal attacks
 * - Format string vulnerabilities
 * - Command injection
 * - Malformed input attacks
 */

// Maximum limits for various inputs (configurable)
#define MAX_INPUT_SIZE (50 * 1024 * 1024)     // 50MB max input
#define MAX_PATH_LENGTH 4096                   // Maximum file path length
#define MAX_FILENAME_LENGTH 255                // Maximum filename component
#define MAX_CIRCUIT_GATES (100 * 1024 * 1024) // 100M gates max
#define MAX_CIRCUIT_INPUTS 1000000             // 1M inputs max
#define MAX_CIRCUIT_OUTPUTS 1000000            // 1M outputs max
#define MAX_WIRE_ID (1000 * 1024 * 1024)      // 1B max wire ID
#define MAX_ARRAY_SIZE (SIZE_MAX / 16)        // Prevent multiplication overflow

// Error codes for validation failures
typedef enum {
    VALIDATION_SUCCESS = 0,
    VALIDATION_NULL_INPUT = -1,
    VALIDATION_SIZE_EXCEEDED = -2,
    VALIDATION_INVALID_CHARS = -3,
    VALIDATION_PATH_TRAVERSAL = -4,
    VALIDATION_INTEGER_OVERFLOW = -5,
    VALIDATION_OUT_OF_BOUNDS = -6,
    VALIDATION_MALFORMED_INPUT = -7,
    VALIDATION_FORBIDDEN_PATH = -8
} validation_result_t;

/**
 * @brief Validate a file path for security
 * 
 * Checks for:
 * - Path traversal attempts (../)
 * - Absolute paths when not allowed
 * - Invalid characters
 * - Path length limits
 * - Forbidden directories
 * 
 * @param path The file path to validate
 * @param allow_absolute Whether absolute paths are permitted
 * @param max_length Maximum allowed path length (0 for default)
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_file_path(const char *path, bool allow_absolute, size_t max_length);

/**
 * @brief Validate and sanitize a filename
 * 
 * Removes dangerous characters and validates length.
 * 
 * @param filename Input filename
 * @param sanitized Output buffer for sanitized filename
 * @param sanitized_size Size of output buffer
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_filename(const char *filename, char *sanitized, size_t sanitized_size);

/**
 * @brief Check for integer overflow in multiplication
 * 
 * Safely checks if a * b would overflow size_t.
 * 
 * @param a First operand
 * @param b Second operand
 * @param result Pointer to store result if no overflow
 * @return true if multiplication is safe, false if overflow would occur
 */
bool safe_multiply(size_t a, size_t b, size_t *result);

/**
 * @brief Check for integer overflow in addition
 * 
 * Safely checks if a + b would overflow size_t.
 * 
 * @param a First operand
 * @param b Second operand
 * @param result Pointer to store result if no overflow
 * @return true if addition is safe, false if overflow would occur
 */
bool safe_add(size_t a, size_t b, size_t *result);

/**
 * @brief Validate array index bounds
 * 
 * @param index The index to check
 * @param array_size Size of the array
 * @return true if index is within bounds, false otherwise
 */
static inline bool validate_array_bounds(size_t index, size_t array_size) {
    return index < array_size;
}

/**
 * @brief Validate pointer and size for buffer operations
 * 
 * @param ptr Pointer to validate
 * @param size Size to validate
 * @param max_size Maximum allowed size (0 for no limit)
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_buffer(const void *ptr, size_t size, size_t max_size);

/**
 * @brief Validate string is null-terminated within bounds
 * 
 * @param str String to validate
 * @param max_len Maximum length to check
 * @return true if properly null-terminated, false otherwise
 */
bool validate_string(const char *str, size_t max_len);

/**
 * @brief Validate circuit parameters
 * 
 * @param num_inputs Number of inputs
 * @param num_outputs Number of outputs
 * @param num_gates Number of gates
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_circuit_params(uint32_t num_inputs, uint32_t num_outputs, uint32_t num_gates);

/**
 * @brief Validate wire ID is within circuit bounds
 * 
 * @param wire_id Wire ID to validate
 * @param max_wire_id Maximum valid wire ID
 * @return true if valid, false otherwise
 */
static inline bool validate_wire_id(uint32_t wire_id, uint32_t max_wire_id) {
    return wire_id <= max_wire_id;
}

/**
 * @brief Validate hexadecimal string
 * 
 * @param hex_str Hex string to validate
 * @param expected_len Expected length (0 for any)
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_hex_string(const char *hex_str, size_t expected_len);

/**
 * @brief Safely allocate memory with overflow checking
 * 
 * @param count Number of elements
 * @param size Size of each element
 * @return Allocated memory or NULL on failure
 */
void* safe_calloc(size_t count, size_t size);

/**
 * @brief Safely reallocate memory with overflow checking
 * 
 * @param ptr Original pointer
 * @param count Number of elements
 * @param size Size of each element
 * @return Reallocated memory or NULL on failure
 */
void* safe_realloc(void *ptr, size_t count, size_t size);

/**
 * @brief Get human-readable error message for validation result
 * 
 * @param result Validation result code
 * @return Error message string
 */
const char* validation_error_string(validation_result_t result);

/**
 * @brief Validate command line argument safety
 * 
 * Checks for shell injection attempts and dangerous characters.
 * 
 * @param arg Command line argument to validate
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_command_arg(const char *arg);

/**
 * @brief Validate numeric string and convert to integer
 * 
 * @param str String to parse
 * @param value Output value
 * @param min Minimum allowed value
 * @param max Maximum allowed value
 * @return VALIDATION_SUCCESS or error code
 */
validation_result_t validate_parse_uint32(const char *str, uint32_t *value, uint32_t min, uint32_t max);

#endif // INPUT_VALIDATION_H