#ifndef CMPTR_CIRCUIT_FORMAT_H
#define CMPTR_CIRCUIT_FORMAT_H

/**
 * @file circuit_format.h
 * @brief Binary format for serializing and deserializing circuits
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include "evaluator.h"

/**
 * @brief Magic number for circuit binary files
 */
#define CIRCUIT_BINARY_MAGIC 0x47434342  // "GCCB" - Gate Computer Circuit Binary

/**
 * @brief Binary format version
 */
#define CIRCUIT_BINARY_VERSION 1

/**
 * @brief Header structure for circuit binary files
 */
typedef struct {
    uint32_t magic;              /**< Magic number (CIRCUIT_BINARY_MAGIC) */
    uint32_t version;            /**< Format version */
    uint32_t header_size;        /**< Size of the header in bytes */
    uint32_t num_inputs;         /**< Number of external inputs */
    uint32_t num_gates;          /**< Number of gates in the circuit */
    uint32_t num_outputs;        /**< Number of circuit outputs */
    uint32_t num_layers;         /**< Number of layers in the circuit */
    uint32_t gates_offset;       /**< Offset to gates array */
    uint32_t outputs_offset;     /**< Offset to output wires array */
    uint32_t layers_offset;      /**< Offset to layer offsets array */
    uint32_t circuit_size;       /**< Total size of the circuit data */
    uint32_t reserved[5];        /**< Reserved for future use */
} circuit_binary_header_t;

/**
 * @brief Gate structure for binary format
 */
typedef struct {
    uint8_t type;                /**< Gate type (GATE_AND or GATE_XOR) */
    uint8_t reserved[3];         /**< Reserved for future use (alignment) */
    uint32_t input1;             /**< First input wire ID */
    uint32_t input2;             /**< Second input wire ID */
    uint32_t output;             /**< Output wire ID */
} circuit_binary_gate_t;

/**
 * @brief Load a circuit from a binary file
 * 
 * @param filename Path to the binary circuit file
 * @return Loaded circuit or NULL on error
 */
circuit_t* circuit_load_binary(const char *filename);

/**
 * @brief Save a circuit to a binary file
 * 
 * @param circuit Circuit to save
 * @param filename Path to the output file
 * @return true if successful, false if error
 */
bool circuit_save_binary(circuit_t *circuit, const char *filename);

/**
 * @brief Get the last error message
 * 
 * @return Error message string
 */
const char* circuit_format_get_error(void);

#endif /* CMPTR_CIRCUIT_FORMAT_H */