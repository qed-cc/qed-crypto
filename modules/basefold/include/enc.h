#ifndef BASEFOLD_ENC_H
#define BASEFOLD_ENC_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include "gf128.h"

// Maximum encoding depth supported
#define MAX_D 32

// Default encoding depth for gate_computer (d=18 for 2^20 gates)
#define D 18

/**
 * Initialize encoding with tweak derivation from transcript
 * 
 * @param transcript_root SHA3-256 hash from Fiat-Shamir transcript (32 bytes)
 * 
 * This function:
 * 1. Derives d non-zero tweaks T₀...T_{d-1} using SHAKE-128(root || j)
 * 2. Computes tweak_digest = SHA3-256(T₀ || ... || T_{d-1})
 * 3. Stores digest in global basefold_proof structure
 * 
 * Must be called before enc_fold() or enc_fold_stream().
 */
void enc_init(const uint8_t transcript_root[32]);

/**
 * In-place Reed-Muller encoding with diagonal tweaks
 * 
 * @param d      Encoding depth (number of fold rounds)
 * @param buf    Input/output buffer containing 2^(d+2) GF(128) words
 * 
 * Transforms raw trace into rate-1/8 foldable Reed-Muller codeword.
 * Input:  2^(d+2) words (e.g., 1M words = 16 MiB for d=18)
 * Output: 8 * 2^d words (e.g., 2M words = 32 MiB for d=18)
 * 
 * Algorithm performs d fold rounds: (L,R) → (L + T_r·R, L - T_r·R)
 * Complexity: O(n) multiplications + XORs per round, total O(n·d)
 */
void enc_fold(size_t d, gf128_t *buf);

/**
 * Streaming Reed-Muller encoding for memory-constrained environments
 * 
 * @param d      Encoding depth
 * @param f_in   Input file containing raw trace
 * @param f_tmp  Temporary file for intermediate results
 * 
 * Performs same encoding as enc_fold() but using bounded memory (≤32 MiB).
 * Processes data in 1 MiB slabs, writing intermediate results to temp file.
 * 
 * Note: This is optional for embedded targets with strict memory limits.
 */
void enc_fold_stream(size_t d, FILE *f_in, FILE *f_tmp);

/**
 * Decode Reed-Muller codeword (inverse of enc_fold)
 * 
 * @param d      Encoding depth
 * @param buf    Codeword buffer to decode in-place
 * 
 * For testing only - reverses the encoding transformation.
 * Used in round-trip tests to verify encoding correctness.
 */
void enc_decode(size_t d, gf128_t *buf);

/**
 * Get tweak value for specific round (internal use)
 * 
 * @param round_index Index of the round (0 to d-1)
 * @return GF(128) tweak value for the specified round
 */
gf128_t enc_get_tweak(size_t round_index);

#endif // BASEFOLD_ENC_H