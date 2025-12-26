/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_CHANNEL_H
#define CMPTR_CHANNEL_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// Key sizes - all SHA3-256 based
#define CMPTR_CHANNEL_KEY_SIZE     32   // 256-bit keys
#define CMPTR_CHANNEL_NONCE_SIZE   16   // 128-bit nonces
#define CMPTR_CHANNEL_TAG_SIZE     32   // SHA3-256 MAC
#define CMPTR_CHANNEL_HEADER_SIZE  48   // Nonce + counter + flags

// Protocol constants
#define CMPTR_CHANNEL_MAX_PACKET   65536
#define CMPTR_CHANNEL_REKEY_AFTER  (1ULL << 20)  // Rekey after 1M packets

// Channel state
typedef struct cmptr_channel cmptr_channel_t;

// Channel role
typedef enum {
    CMPTR_CHANNEL_CLIENT = 0,
    CMPTR_CHANNEL_SERVER = 1
} cmptr_channel_role_t;

// Forward secrecy options
typedef enum {
    CMPTR_CHANNEL_NO_FS = 0,      // No forward secrecy
    CMPTR_CHANNEL_HASH_RATCHET,   // Hash-based ratcheting
    CMPTR_CHANNEL_STARK_RATCHET   // STARK-based (future)
} cmptr_channel_fs_mode_t;

// Channel configuration
typedef struct {
    cmptr_channel_role_t role;
    cmptr_channel_fs_mode_t forward_secrecy;
    uint32_t rekey_interval;      // Packets between rekey (0 = default)
    bool low_latency_mode;        // Optimize for latency vs throughput
} cmptr_channel_config_t;

// Channel statistics
typedef struct {
    uint64_t packets_sent;
    uint64_t packets_received;
    uint64_t bytes_sent;
    uint64_t bytes_received;
    uint64_t rekeys_performed;
    double avg_latency_us;
} cmptr_channel_stats_t;

// Initialize channel with shared secret
cmptr_channel_t* cmptr_channel_init(
    const uint8_t shared_secret[CMPTR_CHANNEL_KEY_SIZE],
    const cmptr_channel_config_t* config
);

// Send encrypted + authenticated packet
bool cmptr_channel_send(
    cmptr_channel_t* channel,
    const uint8_t* plaintext,
    size_t plaintext_len,
    uint8_t* packet_out,
    size_t* packet_len
);

// Receive and verify packet
bool cmptr_channel_recv(
    cmptr_channel_t* channel,
    const uint8_t* packet,
    size_t packet_len,
    uint8_t* plaintext_out,
    size_t* plaintext_len
);

// Manual rekeying
bool cmptr_channel_rekey(cmptr_channel_t* channel);

// Get channel statistics
void cmptr_channel_get_stats(
    const cmptr_channel_t* channel,
    cmptr_channel_stats_t* stats_out
);

// Export channel state (for persistence)
bool cmptr_channel_export(
    const cmptr_channel_t* channel,
    uint8_t* state_out,
    size_t* state_len
);

// Import channel state
cmptr_channel_t* cmptr_channel_import(
    const uint8_t* state,
    size_t state_len
);

// Free channel
void cmptr_channel_free(cmptr_channel_t* channel);

// Utility: Derive initial keys from password (PBKDF2-SHA3)
bool cmptr_channel_derive_key(
    const char* password,
    const uint8_t* salt,
    size_t salt_len,
    uint32_t iterations,
    uint8_t key_out[CMPTR_CHANNEL_KEY_SIZE]
);

// Utility: Constant-time comparison
bool cmptr_channel_ct_equal(
    const uint8_t* a,
    const uint8_t* b,
    size_t len
);

#ifdef __cplusplus
}
#endif

#endif // CMPTR_CHANNEL_H