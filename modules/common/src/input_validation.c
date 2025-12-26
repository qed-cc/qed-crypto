/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * @file input_validation.c
 * @brief Implementation of comprehensive input validation functions
 */

#include "input_validation.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>
#include <errno.h>

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#include <sys/stat.h>
#endif

// Forbidden path components for security
static const char* forbidden_paths[] = {
    "/etc/",
    "/proc/",
    "/sys/",
    "/dev/",
    "/root/",
    "~/.ssh/",
    "~/.gnupg/",
    NULL
};

validation_result_t validate_file_path(const char *path, bool allow_absolute, size_t max_length) {
    if (!path) {
        return VALIDATION_NULL_INPUT;
    }
    
    size_t len = strlen(path);
    if (max_length == 0) {
        max_length = MAX_PATH_LENGTH;
    }
    
    if (len >= max_length) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    // Check for empty path
    if (len == 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Check for absolute paths if not allowed
    if (!allow_absolute && (path[0] == '/' || (len >= 3 && path[1] == ':'))) {
        return VALIDATION_FORBIDDEN_PATH;
    }
    
    // Check for path traversal attempts
    if (strstr(path, "..") != NULL) {
        return VALIDATION_PATH_TRAVERSAL;
    }
    
    // Check for double slashes (can be used to bypass filters)
    if (strstr(path, "//") != NULL) {
        return VALIDATION_INVALID_CHARS;
    }
    
    // Check for forbidden paths
    for (int i = 0; forbidden_paths[i] != NULL; i++) {
        if (strstr(path, forbidden_paths[i]) != NULL) {
            return VALIDATION_FORBIDDEN_PATH;
        }
    }
    
    // Check for invalid characters
    for (size_t i = 0; i < len; i++) {
        char c = path[i];
        // Allow alphanumeric, common path chars, and some special chars
        if (!isalnum(c) && c != '/' && c != '\\' && c != '.' && 
            c != '-' && c != '_' && c != ' ' && c != ':') {
            // Check for control characters
            if (c < 32 || c > 126) {
                return VALIDATION_INVALID_CHARS;
            }
        }
    }
    
    // Check for null bytes
    for (size_t i = 0; i < len; i++) {
        if (path[i] == '\0' && i < len - 1) {
            return VALIDATION_INVALID_CHARS;
        }
    }
    
    return VALIDATION_SUCCESS;
}

validation_result_t validate_filename(const char *filename, char *sanitized, size_t sanitized_size) {
    if (!filename || !sanitized) {
        return VALIDATION_NULL_INPUT;
    }
    
    size_t len = strlen(filename);
    if (len >= MAX_FILENAME_LENGTH || len >= sanitized_size) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    if (len == 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Check for directory separators (filename should not contain paths)
    if (strchr(filename, '/') != NULL || strchr(filename, '\\') != NULL) {
        return VALIDATION_INVALID_CHARS;
    }
    
    // Sanitize filename
    size_t j = 0;
    for (size_t i = 0; i < len && j < sanitized_size - 1; i++) {
        char c = filename[i];
        // Only allow safe characters
        if (isalnum(c) || c == '.' || c == '-' || c == '_') {
            sanitized[j++] = c;
        } else if (c == ' ') {
            sanitized[j++] = '_';  // Replace spaces with underscores
        }
        // Skip other characters
    }
    sanitized[j] = '\0';
    
    // Check if anything was sanitized
    if (j == 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Don't allow files starting with dot (hidden files)
    if (sanitized[0] == '.') {
        return VALIDATION_FORBIDDEN_PATH;
    }
    
    return VALIDATION_SUCCESS;
}

bool safe_multiply(size_t a, size_t b, size_t *result) {
    if (a == 0 || b == 0) {
        if (result) *result = 0;
        return true;
    }
    
    // Check for overflow: a * b > SIZE_MAX
    if (a > SIZE_MAX / b) {
        return false;
    }
    
    if (result) {
        *result = a * b;
    }
    return true;
}

bool safe_add(size_t a, size_t b, size_t *result) {
    // Check for overflow: a + b > SIZE_MAX
    if (a > SIZE_MAX - b) {
        return false;
    }
    
    if (result) {
        *result = a + b;
    }
    return true;
}

validation_result_t validate_buffer(const void *ptr, size_t size, size_t max_size) {
    if (!ptr && size > 0) {
        return VALIDATION_NULL_INPUT;
    }
    
    if (max_size > 0 && size > max_size) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    // Check for suspicious sizes that might indicate integer overflow
    if (size > MAX_ARRAY_SIZE) {
        return VALIDATION_INTEGER_OVERFLOW;
    }
    
    return VALIDATION_SUCCESS;
}

bool validate_string(const char *str, size_t max_len) {
    if (!str) {
        return false;
    }
    
    for (size_t i = 0; i < max_len; i++) {
        if (str[i] == '\0') {
            return true;
        }
    }
    
    return false;  // No null terminator found within max_len
}

validation_result_t validate_circuit_params(uint32_t num_inputs, uint32_t num_outputs, uint32_t num_gates) {
    if (num_inputs > MAX_CIRCUIT_INPUTS) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    if (num_outputs > MAX_CIRCUIT_OUTPUTS) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    if (num_gates > MAX_CIRCUIT_GATES) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    // Basic sanity checks
    if (num_outputs == 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // A circuit with gates should have inputs
    if (num_gates > 0 && num_inputs == 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    return VALIDATION_SUCCESS;
}

validation_result_t validate_hex_string(const char *hex_str, size_t expected_len) {
    if (!hex_str) {
        return VALIDATION_NULL_INPUT;
    }
    
    size_t len = strlen(hex_str);
    
    if (expected_len > 0 && len != expected_len) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    // Hex string should have even length
    if (len % 2 != 0) {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Validate all characters are hex
    for (size_t i = 0; i < len; i++) {
        if (!isxdigit(hex_str[i])) {
            return VALIDATION_INVALID_CHARS;
        }
    }
    
    return VALIDATION_SUCCESS;
}

void* safe_calloc(size_t count, size_t size) {
    size_t total;
    if (!safe_multiply(count, size, &total)) {
        errno = EOVERFLOW;
        return NULL;
    }
    
    return calloc(count, size);
}

void* safe_realloc(void *ptr, size_t count, size_t size) {
    size_t total;
    if (!safe_multiply(count, size, &total)) {
        errno = EOVERFLOW;
        return NULL;
    }
    
    return realloc(ptr, total);
}

const char* validation_error_string(validation_result_t result) {
    switch (result) {
        case VALIDATION_SUCCESS:
            return "Success";
        case VALIDATION_NULL_INPUT:
            return "Null input provided";
        case VALIDATION_SIZE_EXCEEDED:
            return "Size limit exceeded";
        case VALIDATION_INVALID_CHARS:
            return "Invalid characters detected";
        case VALIDATION_PATH_TRAVERSAL:
            return "Path traversal attempt detected";
        case VALIDATION_INTEGER_OVERFLOW:
            return "Integer overflow detected";
        case VALIDATION_OUT_OF_BOUNDS:
            return "Array index out of bounds";
        case VALIDATION_MALFORMED_INPUT:
            return "Malformed input";
        case VALIDATION_FORBIDDEN_PATH:
            return "Forbidden path or filename";
        default:
            return "Unknown validation error";
    }
}

validation_result_t validate_command_arg(const char *arg) {
    if (!arg) {
        return VALIDATION_NULL_INPUT;
    }
    
    size_t len = strlen(arg);
    if (len > MAX_PATH_LENGTH) {
        return VALIDATION_SIZE_EXCEEDED;
    }
    
    // Check for shell metacharacters that could be dangerous
    const char *dangerous_chars = ";|&`$(){}[]<>!#~\"'\\*?";
    
    for (size_t i = 0; i < len; i++) {
        if (strchr(dangerous_chars, arg[i]) != NULL) {
            return VALIDATION_INVALID_CHARS;
        }
        
        // Check for control characters
        if (arg[i] < 32 || arg[i] > 126) {
            return VALIDATION_INVALID_CHARS;
        }
    }
    
    return VALIDATION_SUCCESS;
}

validation_result_t validate_parse_uint32(const char *str, uint32_t *value, uint32_t min, uint32_t max) {
    if (!str || !value) {
        return VALIDATION_NULL_INPUT;
    }
    
    // Check for empty string
    if (*str == '\0') {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Check for negative numbers
    if (*str == '-') {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    char *endptr;
    errno = 0;
    unsigned long long parsed = strtoull(str, &endptr, 10);
    
    // Check for parsing errors
    if (errno == ERANGE || parsed > UINT32_MAX) {
        return VALIDATION_INTEGER_OVERFLOW;
    }
    
    // Check if entire string was parsed
    if (*endptr != '\0') {
        return VALIDATION_MALFORMED_INPUT;
    }
    
    // Check range
    uint32_t result = (uint32_t)parsed;
    if (result < min || result > max) {
        return VALIDATION_OUT_OF_BOUNDS;
    }
    
    *value = result;
    return VALIDATION_SUCCESS;
}