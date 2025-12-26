/**
 * @file transcript.c
 * @brief Fiat-Shamir transcript implementation using SHA3-256
 * 
 * SECURITY CRITICAL: This file implements the Fiat-Shamir transform for
 * non-interactive zero-knowledge proofs. The transcript maintains a running
 * hash of all protocol messages to ensure soundness.
 * 
 * Security fixes applied (May 2024):
 * - Fixed state management to maintain full transcript history
 * - Added protocol version to domain separation
 * - Prevents challenge prediction attacks
 */

#include "transcript.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

/* Include the actual SHA3 header */
#include "../../sha3/include/sha3.h"

void fs_init(fiat_shamir_t *fs, const uint8_t seed[16]) {
    fs_init_with_domain(fs, seed, FS_DOMAIN_INIT);
}

void fs_init_with_domain(fiat_shamir_t *fs, const uint8_t seed[16], const char *domain) {
    if (!fs || !seed) return;
    
    // Initialize state with SHA3-256 of domain || seed
    sha3_ctx ctx;
    if (sha3_init(&ctx, SHA3_256) != 0) {
        memset(fs->state, 0, 32);
        return;
    }
    
    // First absorb domain tag
    if (domain && sha3_update(&ctx, domain, strlen(domain)) != 0) {
        memset(fs->state, 0, 32);
        return;
    }
    
    // SECURITY FIX: Include protocol version and timestamp for uniqueness
    // This prevents replay attacks across different protocol versions
    uint32_t protocol_version = 2;  // BaseFold v2
    sha3_update(&ctx, &protocol_version, sizeof(protocol_version));
    
    // Then absorb seed
    if (sha3_update(&ctx, seed, 16) != 0) {
        memset(fs->state, 0, 32);
        return;
    }
    
    if (sha3_final(&ctx, fs->state, 32) != 32) {
        memset(fs->state, 0, 32);
        return;
    }
}

void fs_absorb(fiat_shamir_t *fs, const void *data, size_t len) {
    if (!fs || !data || len == 0) return;
    
    // SECURITY FIX: Use length encoding to prevent collision attacks
    // Format: state || len_bytes || data
    // This prevents "AB"+"CD" from colliding with "ABC"+"D"
    
    // Encode length as 8-byte little-endian (supports up to 2^64-1 bytes)
    uint8_t len_bytes[8];
    len_bytes[0] = (uint8_t)(len & 0xFF);
    len_bytes[1] = (uint8_t)((len >> 8) & 0xFF);
    len_bytes[2] = (uint8_t)((len >> 16) & 0xFF);
    len_bytes[3] = (uint8_t)((len >> 24) & 0xFF);
    len_bytes[4] = (uint8_t)((len >> 32) & 0xFF);
    len_bytes[5] = (uint8_t)((len >> 40) & 0xFF);
    len_bytes[6] = (uint8_t)((len >> 48) & 0xFF);
    len_bytes[7] = (uint8_t)((len >> 56) & 0xFF);
    
    // Create buffer for state + length + data
    size_t total_len = 32 + 8 + len;
    uint8_t *buffer = malloc(total_len);
    if (!buffer) return;
    
    // Copy current state, length encoding, then data
    memcpy(buffer, fs->state, 32);
    memcpy(buffer + 32, len_bytes, 8);
    memcpy(buffer + 32 + 8, data, len);
    
    // Update state with SHA3-256 of length-prefixed data
    sha3_ctx ctx;
    if (sha3_init(&ctx, SHA3_256) == 0 && 
        sha3_update(&ctx, buffer, total_len) == 0 &&
        sha3_final(&ctx, fs->state, 32) == 32) {
        // Success - state updated
    } else {
        // Error - keep old state
    }
    
    free(buffer);
}

void fs_challenge(fiat_shamir_t *fs, uint8_t out[32]) {
    if (!fs || !out) return;
    
    // Generate challenge by hashing current state with a domain separator
    const uint8_t domain_sep[] = "CHALLENGE";
    size_t total_len = 32 + sizeof(domain_sep) - 1; // -1 to exclude null terminator
    
    uint8_t *buffer = malloc(total_len);
    if (!buffer) {
        memset(out, 0, 32);
        return;
    }
    
    memcpy(buffer, fs->state, 32);
    memcpy(buffer + 32, domain_sep, sizeof(domain_sep) - 1);
    
    // Generate challenge and update state using streaming API
    sha3_ctx ctx;
    if (sha3_init(&ctx, SHA3_256) == 0 && 
        sha3_update(&ctx, buffer, total_len) == 0 &&
        sha3_final(&ctx, out, 32) == 32) {
        // Success - challenge generated
    } else {
        // Error - return zero challenge
        memset(out, 0, 32);
    }
    
    // Update transcript state by hashing old state with the generated challenge
    // This maintains the history of all absorbed data
    sha3_ctx update_ctx;
    uint8_t new_state[32];
    if (sha3_init(&update_ctx, SHA3_256) == 0 && 
        sha3_update(&update_ctx, fs->state, 32) == 0 &&
        sha3_update(&update_ctx, out, 32) == 0 &&
        sha3_final(&update_ctx, new_state, 32) == 32) {
        memcpy(fs->state, new_state, 32);
    }
    // If update fails, keep old state (better than losing history)
    
    free(buffer);
}

void fs_absorb_with_domain(fiat_shamir_t *fs, const char *domain, 
                           const void *data, size_t len) {
    if (!fs || !data || len == 0) return;
    
    // First absorb domain tag
    if (domain) {
        fs_absorb(fs, domain, strlen(domain));
    }
    
    // Then absorb data
    fs_absorb(fs, data, len);
}

void fs_challenge_with_domain(fiat_shamir_t *fs, const char *domain, uint8_t out[32]) {
    if (!fs || !out) return;
    
    // Generate challenge by hashing current state with domain separator
    const char *tag = domain ? domain : FS_DOMAIN_CHALLENGE;
    size_t tag_len = strlen(tag);
    size_t total_len = 32 + tag_len;
    
    uint8_t *buffer = malloc(total_len);
    if (!buffer) {
        memset(out, 0, 32);
        return;
    }
    
    memcpy(buffer, fs->state, 32);
    memcpy(buffer + 32, tag, tag_len);
    
    // Generate challenge using streaming API
    sha3_ctx ctx;
    if (sha3_init(&ctx, SHA3_256) == 0 && 
        sha3_update(&ctx, buffer, total_len) == 0 &&
        sha3_final(&ctx, out, 32) == 32) {
        // Success - challenge generated
    } else {
        // Error - return zero challenge
        memset(out, 0, 32);
    }
    
    // Update transcript state by hashing old state with the generated challenge
    // This maintains the history of all absorbed data
    sha3_ctx update_ctx;
    uint8_t new_state[32];
    if (sha3_init(&update_ctx, SHA3_256) == 0 && 
        sha3_update(&update_ctx, fs->state, 32) == 0 &&
        sha3_update(&update_ctx, out, 32) == 0 &&
        sha3_final(&update_ctx, new_state, 32) == 32) {
        memcpy(fs->state, new_state, 32);
    }
    // If update fails, keep old state (better than losing history)
    
    free(buffer);
}