/**
 * @file prg.h
 * @brief Streaming pseudorandom generator for basefold proofs
 * 
 * Provides AES-CTR based PRG with streaming interface for efficient
 * mask generation and random access seeking.
 */

#ifndef PRG_H
#define PRG_H

#include <stdint.h>

#ifdef __x86_64__
#include <immintrin.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Initialize PRG with 16-byte seed
 * @param seed 128-bit seed for PRG initialization
 * 
 * Call once per proof. Resets internal counter to 0.
 */
void prg_init(const uint8_t seed[16]);

/**
 * @brief Generate next 128-bit pseudorandom block
 * @return Next 128-bit PRG output
 * 
 * Returns consecutive blocks on each call. Internal counter
 * automatically increments.
 */
#ifdef __x86_64__
__m128i prg_next(void);
#else
void prg_next(uint8_t out[16]);
#endif

/**
 * @brief Seek to specific block index for random access
 * @param idx Block index to seek to
 * 
 * Optional function for random access. Next prg_next() call
 * will return block at index idx.
 */
void prg_seek(uint64_t idx);

#ifdef __cplusplus
}
#endif

#endif /* PRG_H */