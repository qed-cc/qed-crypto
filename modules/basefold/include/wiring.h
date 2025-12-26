#ifndef BASEFOLD_WIRING_H
#define BASEFOLD_WIRING_H

/**
 * @file wiring.h
 * @brief Wiring permutation encoding for BaseFold circuit proofs
 * 
 * Encodes the circuit's wiring permutation σ which maps each gate's output
 * to the correct input positions of subsequent gates. This enables the
 * second SumCheck to verify that gate outputs are correctly routed.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

/**
 * @brief Wiring permutation structure
 * 
 * Stores the complete wiring permutation for a circuit with 2^d gates.
 * Each entry sigma[i] gives the destination row index for gate i's output.
 */
typedef struct {
    uint32_t *sigma;           /**< Permutation array: sigma[row] = destination_row */
    uint32_t num_gates;        /**< Number of gates (non-padded) */
    uint32_t padded_size;      /**< Size after padding to 2^d */
    uint32_t d;                /**< Circuit depth parameter */
    bool is_padded;            /**< Whether permutation has been padded */
} wiring_permutation_t;

/**
 * @brief Initialize wiring permutation structure
 * 
 * @param expected_gates Expected number of gates for pre-allocation
 * @return Initialized permutation structure or NULL on error
 */
wiring_permutation_t* wiring_init(uint32_t expected_gates);

/**
 * @brief Free wiring permutation structure
 * 
 * @param wiring Permutation structure to free
 */
void wiring_free(wiring_permutation_t *wiring);

/**
 * @brief Add gate wiring to permutation
 * 
 * @param wiring Permutation structure
 * @param gate_idx Gate index (0-based)
 * @param output_destination Row index where gate output is used as input
 * @return true if added successfully, false on error
 * 
 * Records that gate gate_idx's output feeds into row output_destination.
 * For gates with multiple fanout destinations, call this multiple times.
 */
bool wiring_add_gate(wiring_permutation_t *wiring, uint32_t gate_idx, 
                     uint32_t output_destination);

/**
 * @brief Pad wiring permutation to power of 2
 * 
 * @param wiring Permutation structure to pad
 * @return true if padding successful, false on error
 * 
 * Pads the permutation with identity mappings to reach size 2^d.
 * Required before using in SumCheck protocol.
 */
bool wiring_pad_to_power_of_2(wiring_permutation_t *wiring);

/**
 * @brief Get permutation value for specific gate
 * 
 * @param wiring Permutation structure
 * @param gate_idx Gate index to query
 * @return Destination row index, or UINT32_MAX on error
 */
uint32_t wiring_get_destination(const wiring_permutation_t *wiring, uint32_t gate_idx);

/**
 * @brief Load wiring permutation from circuit netlist
 * 
 * @param circuit_file Path to circuit file in standard format
 * @return Loaded permutation structure or NULL on error
 * 
 * Parses a circuit file and extracts the wiring permutation.
 * Assumes circuit file has gate connectivity information.
 */
wiring_permutation_t* wiring_load_from_circuit(const char *circuit_file);

/**
 * @brief Generate test wiring permutation (for testing only)
 * 
 * @param num_gates Number of gates to generate wiring for
 * @param seed Random seed for generation
 * @return Generated permutation or NULL on error
 * 
 * Creates a random but valid wiring permutation for testing purposes.
 * Ensures all mappings are within valid range.
 */
wiring_permutation_t* wiring_generate_test(uint32_t num_gates, uint32_t seed);

/**
 * @brief Validate wiring permutation
 * 
 * @param wiring Permutation to validate
 * @return true if permutation is valid, false otherwise
 * 
 * Checks that all destination indices are within valid range
 * and that the permutation structure is consistent.
 */
bool wiring_validate(const wiring_permutation_t *wiring);

/**
 * @brief Print wiring permutation summary
 * 
 * @param wiring Permutation to summarize
 */
void wiring_print_summary(const wiring_permutation_t *wiring);

#endif /* BASEFOLD_WIRING_H */