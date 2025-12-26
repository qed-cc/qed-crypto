// sha256_generator.h - pure AND/XOR SHA-256 circuit generator
#ifndef GATE_COMPUTER_SHA256_GENERATOR_H
#define GATE_COMPUTER_SHA256_GENERATOR_H

#include "evaluator.h"

/**
 * @brief Generate a SHA-256 compression circuit using only AND and XOR gates.
 * 
 * Constants 0 and 1 are wire IDs 0 and 1. Message bits are inputs 2..513.
 * Returns a prepared circuit ready for evaluation.
 */
circuit_t* generate_sha256_and_xor_circuit(void);

#endif // GATE_COMPUTER_SHA256_GENERATOR_H