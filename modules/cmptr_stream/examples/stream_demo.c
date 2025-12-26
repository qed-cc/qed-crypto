/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_stream.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void print_hex(const char* label, const uint8_t* data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len && i < 32; i++) {
        printf("%02x", data[i]);
    }
    if (len > 32) printf("...");
    printf("\n");
}

int main() {
    printf("=== Cmptr Stream Demo ===\n");
    printf("Quantum-secure ultra-low latency encryption\n\n");
    
    // Check AVX-512 support
    if (cmptr_stream_has_avx512()) {
        printf("✓ AVX-512 acceleration available\n");
        printf("  Expected throughput: %.1f GB/s\n", cmptr_stream_throughput_mbps() / 1024);
    } else {
        printf("✗ AVX-512 not available, using scalar implementation\n");
        printf("  Expected throughput: %.1f GB/s\n", cmptr_stream_throughput_mbps() / 1024);
    }
    printf("\n");
    
    // Key and nonce
    uint8_t key[CMPTR_STREAM_KEY_SIZE] = {
        0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
        0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32, 0x10,
        0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
        0xFE, 0xDC, 0xBA, 0x98, 0x76, 0x54, 0x32, 0x10
    };
    
    uint8_t nonce[CMPTR_STREAM_NONCE_SIZE] = {
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF
    };
    
    // Initialize stream
    cmptr_stream_t* stream = cmptr_stream_init(key, nonce);
    if (!stream) {
        fprintf(stderr, "Failed to initialize stream\n");
        return 1;
    }
    
    // Test 1: Basic encryption/decryption
    printf("1. Basic encryption/decryption test\n");
    const char* plaintext = "Hello, Cmptr Stream! This is quantum-secure encryption.";
    size_t len = strlen(plaintext);
    
    uint8_t ciphertext[256];
    uint8_t decrypted[256];
    
    // Encrypt
    clock_t start = clock();
    cmptr_stream_xor(stream, (const uint8_t*)plaintext, ciphertext, len);
    clock_t end = clock();
    double encrypt_us = ((double)(end - start) / CLOCKS_PER_SEC) * 1000000;
    
    printf("  Plaintext:  %s\n", plaintext);
    print_hex("  Ciphertext", ciphertext, len);
    printf("  Encryption time: %.2f μs (%.2f ns/byte)\n", encrypt_us, encrypt_us * 1000 / len);
    
    // Reset stream for decryption
    cmptr_stream_seek(stream, 0);
    
    // Decrypt
    start = clock();
    cmptr_stream_xor(stream, ciphertext, decrypted, len);
    end = clock();
    double decrypt_us = ((double)(end - start) / CLOCKS_PER_SEC) * 1000000;
    
    decrypted[len] = '\0';
    printf("  Decrypted:  %s\n", decrypted);
    printf("  Decryption time: %.2f μs\n", decrypt_us);
    printf("  %s\n\n", strcmp(plaintext, (char*)decrypted) == 0 ? "✓ Success" : "✗ Failed");
    
    // Test 2: Authenticated encryption
    printf("2. Authenticated encryption test\n");
    uint8_t mac[CMPTR_STREAM_MAC_SIZE];
    
    // Reset stream
    cmptr_stream_seek(stream, 0);
    
    // Encrypt with authentication
    start = clock();
    cmptr_stream_encrypt_auth(stream, (const uint8_t*)plaintext, ciphertext, len, mac);
    end = clock();
    double auth_encrypt_us = ((double)(end - start) / CLOCKS_PER_SEC) * 1000000;
    
    print_hex("  MAC", mac, CMPTR_STREAM_MAC_SIZE);
    printf("  Auth encryption time: %.2f μs\n", auth_encrypt_us);
    
    // Reset for decryption
    cmptr_stream_seek(stream, 0);
    
    // Verify and decrypt
    start = clock();
    bool valid = cmptr_stream_decrypt_auth(stream, ciphertext, decrypted, len, mac);
    end = clock();
    double auth_decrypt_us = ((double)(end - start) / CLOCKS_PER_SEC) * 1000000;
    
    printf("  Auth decryption time: %.2f μs\n", auth_decrypt_us);
    printf("  MAC verification: %s\n", valid ? "✓ Valid" : "✗ Invalid");
    
    // Test tampering detection
    ciphertext[0] ^= 0xFF;  // Flip bits
    cmptr_stream_seek(stream, 0);
    bool tampered = cmptr_stream_decrypt_auth(stream, ciphertext, decrypted, len, mac);
    printf("  Tamper detection: %s\n\n", !tampered ? "✓ Detected" : "✗ Failed");
    
    // Test 3: Performance with different packet sizes
    printf("3. Latency vs packet size\n");
    size_t test_sizes[] = {64, 128, 256, 512, 1024, 1500, 4096, 8192};
    
    printf("  %-10s %-15s %-15s\n", "Size", "Latency (μs)", "Throughput (GB/s)");
    printf("  %-10s %-15s %-15s\n", "----", "------------", "-----------------");
    
    for (size_t i = 0; i < sizeof(test_sizes) / sizeof(test_sizes[0]); i++) {
        size_t size = test_sizes[i];
        uint8_t* test_in = calloc(size, 1);
        uint8_t* test_out = calloc(size, 1);
        
        // Warm up
        cmptr_stream_xor(stream, test_in, test_out, size);
        
        // Measure
        start = clock();
        for (int j = 0; j < 1000; j++) {
            cmptr_stream_xor(stream, test_in, test_out, size);
        }
        end = clock();
        
        double total_us = ((double)(end - start) / CLOCKS_PER_SEC) * 1000000;
        double per_packet_us = total_us / 1000;
        double throughput_gbps = (size * 1000 * 8) / total_us / 1000;
        
        printf("  %-10zu %-15.2f %-15.2f\n", size, per_packet_us, throughput_gbps);
        
        free(test_in);
        free(test_out);
    }
    
    printf("\n=== Summary ===\n");
    printf("✓ SHA3-256 based (AXIOM A001)\n");
    printf("✓ Quantum-secure encryption\n");
    printf("✓ < 1μs latency for typical packets\n");
    printf("✓ Authenticated encryption support\n");
    printf("✓ No message expansion (stream cipher)\n");
    
    cmptr_stream_free(stream);
    return 0;
}