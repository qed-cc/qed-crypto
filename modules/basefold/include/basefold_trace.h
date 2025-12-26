#ifndef BASEFOLD_TRACE_H
#define BASEFOLD_TRACE_H

/**
 * @file basefold_trace.h
 * @brief Basefold proof system trace recording for gate circuits
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __x86_64__
#include <immintrin.h>
#endif

/**
 * @brief Gate trace entry (4 bits per gate)
 * 
 * Bit layout (LSB to MSB):
 * - Bit 0: Left input bit
 * - Bit 1: Right input bit  
 * - Bit 2: Output bit
 * - Bit 3: Gate type (0 = XOR, 1 = AND)
 */
typedef uint8_t gate_trace_t;

/* Include polynomial types */
#include "polynomial_gf128.h"

/**
 * @brief Basefold trace structure
 * 
 * Stores the complete execution trace of a circuit evaluation
 * for use in generating basefold proofs.
 */
typedef struct basefold_trace_t {
    uint32_t num_gates;           /**< Number of gates traced */
    uint32_t trace_capacity;      /**< Allocated capacity for trace entries */
    gate_trace_t *trace_data;     /**< Packed trace data (4 bits per gate) */
    uint32_t padded_size;         /**< Size after padding to power of 2 */
    uint32_t num_field_elements;  /**< Number of GF(2^128) elements (padded_size * 4) */
#ifdef __x86_64__
    __m128i *field_elements;      /**< Trace as GF(2^128) field elements for masking */
#else
    uint8_t *field_elements;      /**< Trace as 16-byte field elements for masking */
#endif
    bool is_padded;               /**< Whether trace has been padded */
    bool is_masked;               /**< Whether trace has been ZK masked */
    uint8_t mask_seed[128];       /**< 1024-bit CSPRNG seed for masking (paranoid mode) */
    
    /* Polynomial representation for proper ZK */
    poly_gf128_t* witness_polys[4];  /**< L, R, O, S polynomials */
    poly_gf128_t* masked_polys[4];   /**< Randomized witness polynomials */
    poly_gf128_t* randomizer_poly;   /**< Random polynomial r(X) */
    eval_domain_t* eval_domain;      /**< Evaluation domain H */
    
    /* Multilinear polynomial ZK fields */
    uint8_t* zk_seed;             /**< Random seed for polynomial ZK */
    bool needs_polynomial_zk;      /**< Whether to apply polynomial randomization */
    
    /* Extended domain fields for trace ZK */
    uint32_t extended_size;        /**< Size of extended domain (4 * padded_size) */
    uint32_t num_extended_elements; /**< Number of extended field elements */
#ifdef __x86_64__
    __m128i *extended_field_elements; /**< Extended evaluations for ZK */
#else
    uint8_t *extended_field_elements; /**< Extended evaluations for ZK */
#endif
    bool has_extended_elements;    /**< Whether extended elements are computed */
} basefold_trace_t;

/**
 * @brief Trace statistics structure
 */
typedef struct {
    uint32_t total_gates;
    uint32_t and_gates;
    uint32_t xor_gates;
    uint32_t total_bits;
    uint32_t padded_bits;
    double padding_overhead;
} basefold_trace_stats_t;

/**
 * @brief Initialize a basefold trace
 * 
 * @param expected_gates Expected number of gates (for pre-allocation)
 * @return Initialized trace structure or NULL on error
 */
basefold_trace_t* basefold_trace_init(uint32_t expected_gates);

/**
 * @brief Free a basefold trace
 * 
 * @param trace Trace structure to free
 */
void basefold_trace_free(basefold_trace_t *trace);

/**
 * @brief Record a gate execution in the trace
 * 
 * @param trace Trace structure to record to
 * @param left_input Left input bit value (0 or 1)
 * @param right_input Right input bit value (0 or 1)
 * @param output Output bit value (0 or 1)
 * @param gate_type Gate type (0 = XOR, 1 = AND)
 * @return true if recorded successfully, false on error
 */
bool basefold_trace_record_gate(
    basefold_trace_t *trace,
    uint8_t left_input,
    uint8_t right_input,
    uint8_t output,
    uint8_t gate_type
);

/**
 * @brief Pad trace to next power of 2
 * 
 * Pads the trace with zero entries to reach the next power of 2 size.
 * This is required for the basefold proof system.
 * 
 * @param trace Trace structure to pad
 * @return true if padding successful, false on error
 */
bool basefold_trace_pad_to_power_of_2(basefold_trace_t *trace);

/**
 * @brief Get trace data as bit array
 * 
 * Returns the trace data as a contiguous bit array suitable for
 * basefold proof generation. Each gate contributes 4 bits.
 * 
 * @param trace Trace structure
 * @param bit_count Output parameter for total number of bits
 * @return Pointer to bit array or NULL on error
 */
const uint8_t* basefold_trace_get_bits(basefold_trace_t *trace, uint32_t *bit_count);

/**
 * @brief Get trace statistics
 * 
 * @param trace Trace structure
 * @param stats_out Output structure for statistics
 * @return true if successful, false on error
 */
bool basefold_trace_get_stats(basefold_trace_t *trace, basefold_trace_stats_t *stats_out);

/**
 * @brief Print trace summary
 * 
 * @param trace Trace structure to summarize
 */
void basefold_trace_print_summary(basefold_trace_t *trace);

/**
 * @brief Apply zero-knowledge masking to trace
 * 
 * NOTE: Current implementation is incomplete. Proper ZK requires:
 * 1. Polynomial randomization: ŵ(X) = w(X) + v_H(X) · r(X)
 * 2. Mask polynomial R(X) in batching
 * 3. Proper degree bounds based on security parameters
 * 
 * @param trace Trace structure to mask (must be padded)
 * @param seed 16-byte CSPRNG seed (if NULL, generates random seed)
 * @return true if masking successful, false on error
 */
bool basefold_trace_apply_zk_mask(basefold_trace_t *trace, const uint8_t *seed);

/**
 * @brief Compute and store masked polynomial evaluations
 * 
 * This function pre-computes all masked values and stores them in field_elements
 * so the Merkle tree is built from randomized data. This is the key fix for
 * ensuring different proofs have different Merkle roots.
 * 
 * @param trace Trace structure with ZK settings applied
 * @return true if successful, false on error
 */
bool basefold_trace_compute_masked_evaluations(basefold_trace_t* trace);

/**
 * @brief Compute security parameters for zero-knowledge
 * 
 * Computes the required degree for randomizer polynomials based on
 * the formula: h ≥ 2·d·(e·n_F + n_D) + n_D
 * 
 * @param constraint_degree Maximum degree of constraint polynomials
 * @param num_field_queries Number of field queries in protocol
 * @param num_fri_queries Number of FRI queries
 * @return Required degree for randomizer polynomial
 */
size_t basefold_compute_randomizer_degree(size_t constraint_degree,
                                         size_t num_field_queries,
                                         size_t num_fri_queries);

/**
 * @brief Generate a specific mask block on-demand
 * 
 * Regenerates a specific 128-bit mask block using the stored seed.
 * Used during proof verification when specific mask values are needed.
 * 
 * @param trace Masked trace structure
 * @param block_index Index of the 128-bit block to generate
 * @param mask_out Output buffer for 16-byte mask block
 * @return true if successful, false on error
 */
bool basefold_trace_get_mask_block(basefold_trace_t *trace, uint32_t block_index, uint8_t *mask_out);

/**
 * @brief Apply polynomial zero-knowledge using multilinear polynomials
 * 
 * Implements proper polynomial randomization: ŵ(X) = w(X) + v_H(X)·r(X)
 * where v_H is the vanishing polynomial on boolean hypercube.
 * 
 * @param trace Trace structure to apply ZK to (must be padded)
 * @param seed 16-byte random seed (if NULL, generates secure random seed)
 * @return true if successful, false on error
 */
bool basefold_trace_apply_polynomial_zk_multilinear(basefold_trace_t* trace, const uint8_t* seed);

/**
 * @brief Create extended field elements for zero-knowledge trace hiding
 * 
 * Evaluates the trace polynomials on an extended domain that is 4x larger
 * than the original boolean hypercube. The first quadrant contains the
 * original trace values, while the other three quadrants contain randomized
 * values for zero-knowledge.
 * 
 * @param trace Trace structure (must have field_elements and zk_seed)
 * @return true if successful, false on error
 */
bool basefold_trace_create_extended_field_elements(basefold_trace_t* trace);

/**
 * @brief Get the ZK masking seed
 * 
 * Returns a pointer to the 16-byte seed used for masking.
 * This seed must be included in the proof for verification.
 * 
 * @param trace Masked trace structure
 * @return Pointer to 16-byte seed, or NULL if not masked
 */
const uint8_t* basefold_trace_get_mask_seed(basefold_trace_t *trace);

/**
 * @brief Basefold proof container structure
 * 
 * Contains all elements needed for a complete basefold proof:
 * - Mask seed for ZK properties
 * - Merkle root from Reed-Muller encoded trace
 * - Tweak digest from encoding parameters
 * - Additional SumCheck transcripts (to be added in future stages)
 */
typedef struct {
    uint8_t mask_seed[16];       /**< ZK masking seed (already present in trace) */
    uint8_t merkle_root[32];     /**< Merkle root from stage 3 (Reed-Muller encoding) */
    uint8_t tweak_digest[32];    /**< SHA3-256 digest of concatenated tweak list */
    /* Future SumCheck transcripts will be appended here */
} basefold_proof_t;

/**
 * @brief Initialize proof container from trace
 * 
 * @param proof Proof structure to initialize
 * @param trace Source trace (must be masked and padded)
 * @return true if successful, false on error
 */
bool basefold_proof_init(basefold_proof_t *proof, basefold_trace_t *trace);

/**
 * @brief Set Merkle root in proof
 * 
 * @param proof Proof structure
 * @param merkle_root 32-byte Merkle root from Reed-Muller encoding
 * @return true if successful, false on error
 */
bool basefold_proof_set_merkle_root(basefold_proof_t *proof, const uint8_t merkle_root[32]);

/**
 * @brief Set tweak digest in proof
 * 
 * @param proof Proof structure
 * @param tweak_digest 32-byte SHA3-256 digest of tweak parameters
 * @return true if successful, false on error
 */
bool basefold_proof_set_tweak_digest(basefold_proof_t *proof, const uint8_t tweak_digest[32]);

#endif /* BASEFOLD_TRACE_H */