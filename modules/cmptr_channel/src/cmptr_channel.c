/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_channel.h"
#include "../../cmptr_stream/include/cmptr_stream.h"
#include "../../sha3/include/sha3.h"
#include "../../common/include/secure_random.h"
#include <stdlib.h>
#include <string.h>

// Packet format:
// [16 bytes nonce][8 bytes counter][8 bytes flags][encrypted data][32 bytes MAC]

#define PACKET_NONCE_OFFSET    0
#define PACKET_COUNTER_OFFSET  16
#define PACKET_FLAGS_OFFSET    24
#define PACKET_DATA_OFFSET     32

// Channel state
struct cmptr_channel {
    // Configuration
    cmptr_channel_config_t config;
    
    // Current keys
    uint8_t send_key[CMPTR_CHANNEL_KEY_SIZE];
    uint8_t recv_key[CMPTR_CHANNEL_KEY_SIZE];
    
    // Ratchet keys (for forward secrecy)
    uint8_t ratchet_key[CMPTR_CHANNEL_KEY_SIZE];
    
    // Counters
    uint64_t send_counter;
    uint64_t recv_counter;
    uint64_t rekey_counter;
    
    // Statistics
    cmptr_channel_stats_t stats;
    
    // Stream ciphers
    cmptr_stream_t* send_stream;
    cmptr_stream_t* recv_stream;
};

// Derive send/recv keys from shared secret
static void derive_directional_keys(
    const uint8_t shared_secret[CMPTR_CHANNEL_KEY_SIZE],
    cmptr_channel_role_t role,
    uint8_t send_key[CMPTR_CHANNEL_KEY_SIZE],
    uint8_t recv_key[CMPTR_CHANNEL_KEY_SIZE]
) {
    sha3_ctx ctx;
    
    // Client send key = SHA3("client_send" || shared_secret)
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"client_send", 11);
    sha3_update(&ctx, shared_secret, CMPTR_CHANNEL_KEY_SIZE);
    sha3_final(&ctx, role == CMPTR_CHANNEL_CLIENT ? send_key : recv_key, 32);
    
    // Server send key = SHA3("server_send" || shared_secret)
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"server_send", 11);
    sha3_update(&ctx, shared_secret, CMPTR_CHANNEL_KEY_SIZE);
    sha3_final(&ctx, role == CMPTR_CHANNEL_SERVER ? send_key : recv_key, 32);
}

// Hash ratcheting for forward secrecy
static void ratchet_key(uint8_t key[CMPTR_CHANNEL_KEY_SIZE]) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)"ratchet", 7);
    sha3_update(&ctx, key, CMPTR_CHANNEL_KEY_SIZE);
    sha3_final(&ctx, key, 32);
}

cmptr_channel_t* cmptr_channel_init(
    const uint8_t shared_secret[CMPTR_CHANNEL_KEY_SIZE],
    const cmptr_channel_config_t* config
) {
    cmptr_channel_t* channel = calloc(1, sizeof(cmptr_channel_t));
    if (!channel) return NULL;
    
    // Copy config
    if (config) {
        channel->config = *config;
    } else {
        // Default config
        channel->config.role = CMPTR_CHANNEL_CLIENT;
        channel->config.forward_secrecy = CMPTR_CHANNEL_HASH_RATCHET;
        channel->config.rekey_interval = CMPTR_CHANNEL_REKEY_AFTER;
        channel->config.low_latency_mode = true;
    }
    
    // Derive directional keys
    derive_directional_keys(
        shared_secret,
        channel->config.role,
        channel->send_key,
        channel->recv_key
    );
    
    // Initialize ratchet key
    memcpy(channel->ratchet_key, shared_secret, CMPTR_CHANNEL_KEY_SIZE);
    
    // Initialize counters
    channel->send_counter = 0;
    channel->recv_counter = 0;
    channel->rekey_counter = 0;
    
    return channel;
}

bool cmptr_channel_send(
    cmptr_channel_t* channel,
    const uint8_t* plaintext,
    size_t plaintext_len,
    uint8_t* packet_out,
    size_t* packet_len
) {
    if (!channel || !plaintext || !packet_out || !packet_len) {
        return false;
    }
    
    // Check packet size
    if (plaintext_len > CMPTR_CHANNEL_MAX_PACKET - CMPTR_CHANNEL_HEADER_SIZE - CMPTR_CHANNEL_TAG_SIZE) {
        return false;
    }
    
    // Generate nonce
    uint8_t nonce[CMPTR_CHANNEL_NONCE_SIZE];
    if (secure_random_bytes(nonce, CMPTR_CHANNEL_NONCE_SIZE) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    
    // Build packet header
    memcpy(packet_out + PACKET_NONCE_OFFSET, nonce, CMPTR_CHANNEL_NONCE_SIZE);
    memcpy(packet_out + PACKET_COUNTER_OFFSET, &channel->send_counter, 8);
    uint64_t flags = 0;  // Reserved for future use
    memcpy(packet_out + PACKET_FLAGS_OFFSET, &flags, 8);
    
    // Create stream cipher for this packet
    if (channel->send_stream) {
        cmptr_stream_free(channel->send_stream);
    }
    channel->send_stream = cmptr_stream_init(channel->send_key, nonce);
    if (!channel->send_stream) {
        return false;
    }
    
    // Encrypt data
    cmptr_stream_xor(
        channel->send_stream,
        plaintext,
        packet_out + PACKET_DATA_OFFSET,
        plaintext_len
    );
    
    // Compute MAC over entire packet (header + ciphertext)
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, channel->send_key, CMPTR_CHANNEL_KEY_SIZE);
    sha3_update(&ctx, packet_out, PACKET_DATA_OFFSET + plaintext_len);
    sha3_final(&ctx, packet_out + PACKET_DATA_OFFSET + plaintext_len, 32);
    
    // Update packet length
    *packet_len = PACKET_DATA_OFFSET + plaintext_len + CMPTR_CHANNEL_TAG_SIZE;
    
    // Update statistics
    channel->stats.packets_sent++;
    channel->stats.bytes_sent += plaintext_len;
    channel->send_counter++;
    
    // Check if rekeying needed
    if (channel->config.rekey_interval > 0 && 
        channel->send_counter % channel->config.rekey_interval == 0) {
        cmptr_channel_rekey(channel);
    }
    
    return true;
}

bool cmptr_channel_recv(
    cmptr_channel_t* channel,
    const uint8_t* packet,
    size_t packet_len,
    uint8_t* plaintext_out,
    size_t* plaintext_len
) {
    if (!channel || !packet || !plaintext_out || !plaintext_len) {
        return false;
    }
    
    // Minimum packet size check
    if (packet_len < PACKET_DATA_OFFSET + CMPTR_CHANNEL_TAG_SIZE) {
        return false;
    }
    
    size_t ciphertext_len = packet_len - PACKET_DATA_OFFSET - CMPTR_CHANNEL_TAG_SIZE;
    
    // Verify MAC
    sha3_ctx ctx;
    uint8_t expected_mac[CMPTR_CHANNEL_TAG_SIZE];
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, channel->recv_key, CMPTR_CHANNEL_KEY_SIZE);
    sha3_update(&ctx, packet, PACKET_DATA_OFFSET + ciphertext_len);
    sha3_final(&ctx, expected_mac, 32);
    
    // Constant-time MAC comparison
    if (!cmptr_channel_ct_equal(
        expected_mac,
        packet + PACKET_DATA_OFFSET + ciphertext_len,
        CMPTR_CHANNEL_TAG_SIZE
    )) {
        return false;  // MAC verification failed
    }
    
    // Extract nonce and counter
    uint8_t nonce[CMPTR_CHANNEL_NONCE_SIZE];
    memcpy(nonce, packet + PACKET_NONCE_OFFSET, CMPTR_CHANNEL_NONCE_SIZE);
    
    uint64_t packet_counter;
    memcpy(&packet_counter, packet + PACKET_COUNTER_OFFSET, 8);
    
    // Create stream cipher for decryption
    if (channel->recv_stream) {
        cmptr_stream_free(channel->recv_stream);
    }
    channel->recv_stream = cmptr_stream_init(channel->recv_key, nonce);
    if (!channel->recv_stream) {
        return false;
    }
    
    // Decrypt data
    cmptr_stream_xor(
        channel->recv_stream,
        packet + PACKET_DATA_OFFSET,
        plaintext_out,
        ciphertext_len
    );
    
    *plaintext_len = ciphertext_len;
    
    // Update statistics
    channel->stats.packets_received++;
    channel->stats.bytes_received += ciphertext_len;
    channel->recv_counter = packet_counter + 1;
    
    return true;
}

bool cmptr_channel_rekey(cmptr_channel_t* channel) {
    if (!channel) return false;
    
    // Apply hash ratcheting to all keys
    if (channel->config.forward_secrecy == CMPTR_CHANNEL_HASH_RATCHET) {
        ratchet_key(channel->send_key);
        ratchet_key(channel->recv_key);
        ratchet_key(channel->ratchet_key);
    }
    
    channel->rekey_counter++;
    channel->stats.rekeys_performed++;
    
    return true;
}

void cmptr_channel_get_stats(
    const cmptr_channel_t* channel,
    cmptr_channel_stats_t* stats_out
) {
    if (channel && stats_out) {
        *stats_out = channel->stats;
    }
}

void cmptr_channel_free(cmptr_channel_t* channel) {
    if (!channel) return;
    
    if (channel->send_stream) {
        cmptr_stream_free(channel->send_stream);
    }
    if (channel->recv_stream) {
        cmptr_stream_free(channel->recv_stream);
    }
    
    // Clear sensitive data
    memset(channel->send_key, 0, sizeof(channel->send_key));
    memset(channel->recv_key, 0, sizeof(channel->recv_key));
    memset(channel->ratchet_key, 0, sizeof(channel->ratchet_key));
    
    free(channel);
}

bool cmptr_channel_derive_key(
    const char* password,
    const uint8_t* salt,
    size_t salt_len,
    uint32_t iterations,
    uint8_t key_out[CMPTR_CHANNEL_KEY_SIZE]
) {
    if (!password || !salt || !key_out || iterations == 0) {
        return false;
    }
    
    // PBKDF2-SHA3-256 implementation
    uint8_t u[CMPTR_CHANNEL_KEY_SIZE];
    uint8_t t[CMPTR_CHANNEL_KEY_SIZE];
    memset(t, 0, CMPTR_CHANNEL_KEY_SIZE);
    
    // PRF = HMAC-SHA3-256
    for (uint32_t i = 0; i < iterations; i++) {
        sha3_ctx ctx;
        sha3_init(&ctx, SHA3_256);
        
        if (i == 0) {
            // First iteration: PRF(password, salt || 0x00000001)
            sha3_update(&ctx, (const uint8_t*)password, strlen(password));
            sha3_update(&ctx, salt, salt_len);
            uint32_t counter = 1;
            sha3_update(&ctx, (const uint8_t*)&counter, 4);
        } else {
            // Subsequent iterations: PRF(password, u)
            sha3_update(&ctx, (const uint8_t*)password, strlen(password));
            sha3_update(&ctx, u, CMPTR_CHANNEL_KEY_SIZE);
        }
        
        sha3_final(&ctx, u, 32);
        
        // XOR with running result
        for (size_t j = 0; j < CMPTR_CHANNEL_KEY_SIZE; j++) {
            t[j] ^= u[j];
        }
    }
    
    memcpy(key_out, t, CMPTR_CHANNEL_KEY_SIZE);
    return true;
}

bool cmptr_channel_ct_equal(const uint8_t* a, const uint8_t* b, size_t len) {
    uint8_t diff = 0;
    for (size_t i = 0; i < len; i++) {
        diff |= a[i] ^ b[i];
    }
    return diff == 0;
}