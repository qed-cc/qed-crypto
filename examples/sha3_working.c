/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "sha3.h"

int main() {
    printf("=== SHA3 Working Example ===\n\n");
    
    // Example 1: Hash a simple string
    const char* message = "Hello CMPTR!";
    uint8_t hash[SHA3_256_DIGEST_SIZE];
    
    sha3_hash(SHA3_256, message, strlen(message), hash, sizeof(hash));
    
    printf("Message: %s\n", message);
    printf("SHA3-256: ");
    for (int i = 0; i < SHA3_256_DIGEST_SIZE; i++) {
        printf("%02x", hash[i]);
    }
    printf("\n\n");
    
    // Example 2: Hash binary data
    uint8_t data[] = {0x01, 0x02, 0x03, 0x04, 0x05};
    sha3_hash(SHA3_256, data, sizeof(data), hash, sizeof(hash));
    
    printf("Binary data: ");
    for (size_t i = 0; i < sizeof(data); i++) {
        printf("%02x ", data[i]);
    }
    printf("\nSHA3-256: ");
    for (int i = 0; i < SHA3_256_DIGEST_SIZE; i++) {
        printf("%02x", hash[i]);
    }
    printf("\n\n");
    
    // Example 3: Different SHA3 variants
    uint8_t hash224[SHA3_224_DIGEST_SIZE];
    uint8_t hash384[SHA3_384_DIGEST_SIZE];
    uint8_t hash512[SHA3_512_DIGEST_SIZE];
    
    sha3_hash(SHA3_224, message, strlen(message), hash224, sizeof(hash224));
    sha3_hash(SHA3_384, message, strlen(message), hash384, sizeof(hash384));
    sha3_hash(SHA3_512, message, strlen(message), hash512, sizeof(hash512));
    
    printf("SHA3-224: ");
    for (int i = 0; i < SHA3_224_DIGEST_SIZE; i++) printf("%02x", hash224[i]);
    printf("\n");
    
    printf("SHA3-384: ");
    for (int i = 0; i < SHA3_384_DIGEST_SIZE; i++) printf("%02x", hash384[i]);
    printf("\n");
    
    printf("SHA3-512: ");
    for (int i = 0; i < SHA3_512_DIGEST_SIZE; i++) printf("%02x", hash512[i]);
    printf("\n");
    
    printf("\n✅ All SHA3 operations completed successfully!\n");
    return 0;
}