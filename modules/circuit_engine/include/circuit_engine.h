#ifndef CIRCUIT_ENGINE_H
#define CIRCUIT_ENGINE_H

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <evaluator.h>

/**
 * @brief SHA3 type enumeration
 */
typedef enum {
    SHA3_256 /**< SHA3-256: 256-bit output */
} sha3_type_t;

/**
 * @brief Get the maximum user-visible input size for SHA3-256
 * 
 * @param type SHA3 variant (only SHA3-256 supported)
 * @return Maximum input size in bits before padding
 */
uint32_t sha3_get_user_input_size(sha3_type_t type);

/**
 * @brief Get the input size for SHA3-256 (rate)
 * 
 * @param type SHA3 variant (only SHA3-256 supported)
 * @return Rate in bits (1088 for SHA3-256)
 */
uint32_t sha3_get_input_size(sha3_type_t type);

/**
 * @brief Get the output size for SHA3-256
 * 
 * @param type SHA3 variant (only SHA3-256 supported)
 * @return Output size in bits (256 for SHA3-256)
 */
uint32_t sha3_get_output_size(sha3_type_t type);

/**
 * @brief Generate a SHA3-256 circuit
 * 
 * This function generates a gate circuit for SHA3-256 hash function.
 * The circuit takes up to 1088 input bits (the rate) and produces a 256-bit output.
 * The implementation follows the FIPS 202 standard with proper padding and bit ordering.
 * 
 * @param type SHA3 type (only SHA3-256 is supported)
 * @return Pointer to the generated circuit, or NULL on error
 */
circuit_t* generate_sha3_circuit(sha3_type_t type);

/**
 * @brief Evaluate the SHA3-256 circuit
 * 
 * This function evaluates a SHA3-256 circuit with the provided input,
 * adding proper padding (domain separator 0x06 and end bit 0x80).
 * 
 * @param circuit SHA3-256 circuit to evaluate
 * @param input Input data (up to 136 bytes)
 * @param input_len Input data length
 * @param output Output buffer (must be 32 bytes for SHA3-256)
 * @return true if evaluation was successful, false otherwise
 */
bool evaluate_sha3_circuit(circuit_t *circuit, const uint8_t *input, size_t input_len, uint8_t *output);

#endif /* CIRCUIT_ENGINE_H */