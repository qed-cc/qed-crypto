#ifndef CMPTR_CIRCUIT_IO_H
#define CMPTR_CIRCUIT_IO_H

/**
 * @file circuit_io.h
 * @brief Simple circuit I/O interface for standalone mode
 */

#include <stdint.h>
#include <stdbool.h>
#include "evaluator.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Parse a circuit from a file
 * 
 * @param filename Path to the circuit file
 * @return Parsed circuit or NULL on error
 */
circuit_t* circuit_io_parse_file(const char *filename);

/**
 * @brief Get the last error message
 * 
 * @return Error message string
 */
const char* circuit_io_get_error(void);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_CIRCUIT_IO_H */