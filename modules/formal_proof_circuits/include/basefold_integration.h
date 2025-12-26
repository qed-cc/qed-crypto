/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#ifndef BASEFOLD_INTEGRATION_H
#define BASEFOLD_INTEGRATION_H

#include "formal_proof_circuits.h"
#include "../../basefold_raa/include/basefold_raa.h"
#include "../../circuit_evaluator/include/evaluator.h"
#include <stdint.h>
#include <stdbool.h>

/**
 * @file basefold_integration.h
 * @brief Integration layer between formal proof circuits and BaseFold RAA
 * 
 * This module provides the bridge between theoretical formal proofs
 * and computational cryptographic proofs with 121-bit security.
 */

/**
 * @brief Convert proof_circuit_t to gate_computer circuit format
 * 
 * Maps logical gates (AND, OR, NOT, etc.) to arithmetic constraints
 * over GF(2^128) that BaseFold RAA can prove.
 * 
 * @param proof_circuit Input formal proof circuit
 * @param circuit Output circuit in gate_computer format
 * @return 0 on success, negative on error
 */
int convert_to_gate_circuit(const proof_circuit_t* proof_circuit,
                           circuit_t* circuit);

/**
 * @brief Generate witness for BaseFold RAA from logical witness
 * 
 * Converts boolean witness values to GF(2^128) elements and ensures
 * all constraints are satisfied.
 * 
 * @param proof_circuit Circuit structure
 * @param logical_witness Boolean witness values (0 or 1)
 * @param gf_witness Output witness in GF(2^128) (preallocated)
 * @param witness_size Size of witness arrays
 * @return 0 on success, negative on error
 */
int convert_witness_to_gf128(const proof_circuit_t* proof_circuit,
                            const uint8_t* logical_witness,
                            gf128_t* gf_witness,
                            size_t witness_size);

/**
 * @brief Generate cryptographic proof for formal statement
 * 
 * This is the main integration function that:
 * 1. Converts the formal circuit to arithmetic form
 * 2. Generates appropriate witness in GF(2^128)
 * 3. Calls basefold_raa_prove() with proper configuration
 * 4. Returns the cryptographic proof
 * 
 * @param proof_circuit Formal proof circuit
 * @param logical_witness Boolean witness (may be NULL for tautologies)
 * @param enable_zk Enable zero-knowledge (always 1 per Axiom A002)
 * @param proof_out Output buffer for proof
 * @param proof_size_out Size of generated proof
 * @return 0 on success, negative on error
 */
int generate_basefold_proof(const proof_circuit_t* proof_circuit,
                           const uint8_t* logical_witness,
                           int enable_zk,
                           uint8_t** proof_out,
                           size_t* proof_size_out);

/**
 * @brief Verify cryptographic proof of formal statement
 * 
 * @param proof_circuit Original formal circuit
 * @param proof Cryptographic proof to verify
 * @param proof_size Size of proof
 * @return 0 if valid, negative if invalid
 */
int verify_basefold_proof(const proof_circuit_t* proof_circuit,
                         const uint8_t* proof,
                         size_t proof_size);

/**
 * @brief Estimate proof size for planning
 * 
 * @param proof_circuit Circuit to analyze
 * @return Estimated proof size in bytes
 */
size_t estimate_proof_size(const proof_circuit_t* proof_circuit);

/**
 * @brief Serialize proof for storage/transmission
 * 
 * @param proof BaseFold RAA proof structure
 * @param buffer Output buffer (preallocated)
 * @param buffer_size Size of buffer
 * @return Actual size written, or negative on error
 */
ssize_t serialize_basefold_proof(const basefold_raa_proof_t* proof,
                                uint8_t* buffer,
                                size_t buffer_size);

/**
 * @brief Deserialize proof from buffer
 * 
 * @param buffer Input buffer
 * @param buffer_size Size of buffer
 * @param proof Output proof structure
 * @return 0 on success, negative on error
 */
int deserialize_basefold_proof(const uint8_t* buffer,
                              size_t buffer_size,
                              basefold_raa_proof_t* proof);

/**
 * @brief Configuration for witness generation
 */
typedef struct {
    int max_iterations;      // Max SAT solver iterations
    int use_random_search;   // Enable random search
    int num_threads;         // Parallelism for search
    uint64_t timeout_ms;     // Timeout in milliseconds
} witness_config_t;

/**
 * @brief Generate witness for existential statements
 * 
 * Uses a SAT solver to find satisfying assignment for circuits
 * with existential quantifiers.
 * 
 * @param proof_circuit Circuit with existential quantifiers
 * @param config Configuration for witness search
 * @param witness Output witness (preallocated)
 * @return 0 if witness found, negative if UNSAT or timeout
 */
int generate_existential_witness(const proof_circuit_t* proof_circuit,
                                const witness_config_t* config,
                                uint8_t* witness);

/**
 * @brief Get default configuration
 */
void get_default_witness_config(witness_config_t* config);

#endif // BASEFOLD_INTEGRATION_H