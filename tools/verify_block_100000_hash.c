/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <openssl/sha.h>

// Convert hex string to bytes
int hex_to_bytes(const char* hex, uint8_t* bytes, size_t max_bytes) {
    size_t hex_len = strlen(hex);
    if (hex_len % 2 != 0 || hex_len / 2 > max_bytes) {
        return -1;
    }
    
    for (size_t i = 0; i < hex_len; i += 2) {
        sscanf(hex + i, "%2hhx", &bytes[i / 2]);
    }
    return hex_len / 2;
}

// Print bytes as hex
void print_hex(const uint8_t* bytes, size_t len) {
    for (size_t i = 0; i < len; i++) {
        printf("%02x", bytes[i]);
    }
}

// Print bytes as hex in reverse order (for Bitcoin hashes)
void print_hex_reverse(const uint8_t* bytes, size_t len) {
    for (int i = len - 1; i >= 0; i--) {
        printf("%02x", bytes[i]);
    }
}

int main() {
    // Bitcoin Block #100000 header (80 bytes)
    const char* header_hex = "0100000050120119172a610421a6c3011dd330d9df07b63616c2cc1f1cd00200000000006657a9252aacd5c0b2940996ecff952228c3067cc38d4885efb5a4ac4247e9f337221b4d4c86041b0f2b5710";
    
    printf("Bitcoin Block #100000 Header Verification\n");
    printf("==========================================\n\n");
    
    // Convert hex to bytes
    uint8_t header_bytes[80];
    int header_len = hex_to_bytes(header_hex, header_bytes, 80);
    if (header_len != 80) {
        printf("Error: Invalid header length\n");
        return 1;
    }
    
    printf("Header (80 bytes): %s\n\n", header_hex);
    
    // Parse header fields
    uint32_t version = *(uint32_t*)&header_bytes[0];
    printf("Version: %u\n", version);
    
    printf("Previous hash: ");
    print_hex_reverse(&header_bytes[4], 32);
    printf("\n");
    
    printf("Merkle root: ");
    print_hex_reverse(&header_bytes[36], 32);
    printf("\n");
    
    uint32_t timestamp = *(uint32_t*)&header_bytes[68];
    printf("Timestamp: %u\n", timestamp);
    
    uint32_t bits = *(uint32_t*)&header_bytes[72];
    printf("Bits: 0x%08x\n", bits);
    
    uint32_t nonce = *(uint32_t*)&header_bytes[76];
    printf("Nonce: %u\n\n", nonce);
    
    // Calculate double SHA-256
    uint8_t hash1[32];
    uint8_t hash2[32];
    
    SHA256(header_bytes, 80, hash1);
    SHA256(hash1, 32, hash2);
    
    printf("Calculated hash: ");
    print_hex_reverse(hash2, 32);
    printf("\n");
    
    printf("Expected hash:   000000000003ba27aa200b1cecaad478d2b00432346c3f1f3986da1afd33e506\n");
    
    // Compare with expected hash
    const char* expected_hex = "000000000003ba27aa200b1cecaad478d2b00432346c3f1f3986da1afd33e506";
    uint8_t expected[32];
    hex_to_bytes(expected_hex, expected, 32);
    
    // Reverse expected hash for comparison (Bitcoin displays hashes reversed)
    uint8_t expected_reversed[32];
    for (int i = 0; i < 32; i++) {
        expected_reversed[i] = expected[31 - i];
    }
    
    if (memcmp(hash2, expected_reversed, 32) == 0) {
        printf("\n✅ HASH VERIFICATION SUCCESSFUL!\n");
    } else {
        printf("\n❌ HASH MISMATCH!\n");
    }
    
    return 0;
}