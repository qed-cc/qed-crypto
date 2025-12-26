/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_STREAM_H
#define CMPTR_STREAM_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file cmptr_stream.h
 * @brief Ultra-low latency quantum-secure stream cipher
 * 
 * Cmptr Stream provides < 1μs encryption latency using SHA3-256 in counter mode
 * with AVX-512 acceleration. Designed for real-time communication channels.
 * 
 * Security: 256-bit keys, requires unique nonces, quantum-secure
 * Performance: 10+ Gbps throughput, < 1μs latency per 512-byte packet
 */

// Constants
#define CMPTR_STREAM_KEY_SIZE    32  // 256-bit keys
#define CMPTR_STREAM_NONCE_SIZE  16  // 128-bit nonces
#define CMPTR_STREAM_BLOCK_SIZE  32  // SHA3-256 output
#define CMPTR_STREAM_MAC_SIZE    32  // SHA3-256 MAC

// Forward declaration
typedef struct cmptr_stream cmptr_stream_t;

// Stream cipher states
typedef enum {
    CMPTR_STREAM_ENCRYPT = 0,
    CMPTR_STREAM_DECRYPT = 1
} cmptr_stream_mode_t;

/**
 * @brief Initialize a stream cipher instance
 * @param key 256-bit encryption key
 * @param nonce 128-bit unique nonce (MUST be unique per key)
 * @return Stream instance or NULL on error
 */
cmptr_stream_t* cmptr_stream_init(const uint8_t key[CMPTR_STREAM_KEY_SIZE],
                                   const uint8_t nonce[CMPTR_STREAM_NONCE_SIZE]);

/**
 * @brief Free stream cipher instance
 * @param stream Stream to free
 */
void cmptr_stream_free(cmptr_stream_t* stream);

/**
 * @brief Encrypt/decrypt data (same operation for stream cipher)
 * @param stream Stream instance
 * @param input Input data
 * @param output Output buffer (can be same as input for in-place)
 * @param len Length in bytes
 * @return true on success
 */
bool cmptr_stream_xor(cmptr_stream_t* stream,
                      const uint8_t* input,
                      uint8_t* output,
                      size_t len);

/**
 * @brief Encrypt and authenticate data
 * @param stream Stream instance
 * @param plaintext Input plaintext
 * @param ciphertext Output ciphertext buffer
 * @param len Length of plaintext
 * @param mac Output MAC (32 bytes)
 * @return true on success
 */
bool cmptr_stream_encrypt_auth(cmptr_stream_t* stream,
                               const uint8_t* plaintext,
                               uint8_t* ciphertext,
                               size_t len,
                               uint8_t mac[CMPTR_STREAM_MAC_SIZE]);

/**
 * @brief Decrypt and verify authenticated data
 * @param stream Stream instance
 * @param ciphertext Input ciphertext
 * @param plaintext Output plaintext buffer
 * @param len Length of ciphertext
 * @param mac Expected MAC (32 bytes)
 * @return true if MAC valid and decryption successful
 */
bool cmptr_stream_decrypt_auth(cmptr_stream_t* stream,
                               const uint8_t* ciphertext,
                               uint8_t* plaintext,
                               size_t len,
                               const uint8_t mac[CMPTR_STREAM_MAC_SIZE]);

/**
 * @brief Set counter position (for seeking in stream)
 * @param stream Stream instance
 * @param counter New counter value
 */
void cmptr_stream_seek(cmptr_stream_t* stream, uint64_t counter);

/**
 * @brief Get current counter position
 * @param stream Stream instance
 * @return Current counter value
 */
uint64_t cmptr_stream_tell(const cmptr_stream_t* stream);

// Performance utilities

/**
 * @brief Check if AVX-512 acceleration is available
 * @return true if AVX-512 available
 */
bool cmptr_stream_has_avx512(void);

/**
 * @brief Get encryption throughput estimate
 * @return Throughput in MB/s
 */
double cmptr_stream_throughput_mbps(void);

/**
 * @brief Benchmark encryption latency
 * @param packet_size Size of packets to test
 * @return Latency in microseconds
 */
double cmptr_stream_latency_us(size_t packet_size);

// Bulk operations for maximum performance

/**
 * @brief Process multiple packets in parallel (AVX-512 optimized)
 * @param streams Array of stream instances (up to 8)
 * @param inputs Array of input buffers
 * @param outputs Array of output buffers
 * @param lens Array of lengths
 * @param count Number of streams (1-8)
 * @return true on success
 */
bool cmptr_stream_bulk_xor(cmptr_stream_t** streams,
                           const uint8_t** inputs,
                           uint8_t** outputs,
                           const size_t* lens,
                           size_t count);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_STREAM_H