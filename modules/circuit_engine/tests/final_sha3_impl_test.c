#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include "src/sha3_final.h"

// NIST test vectors for SHA3-256
typedef struct {
    const char *message;
    size_t message_len;
    const uint8_t hash[32];
} test_vector_t;

static const test_vector_t test_vectors[] = {
    // Empty string
    {
        "",
        0,
        {
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56,
            0xa0, 0x61, 0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
            0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a
        }
    },
    // "abc"
    {
        "abc",
        3,
        {
            0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d,
            0x6b, 0xd3, 0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b,
            0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43, 0x15, 0x32
        }
    },
    // "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
    {
        "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        56,
        {
            0x41, 0xc0, 0xdb, 0xa2, 0xa9, 0xd6, 0x24, 0x08, 0x49, 0x10, 0x03, 0x76,
            0xa8, 0x23, 0x5e, 0x2c, 0x82, 0xe1, 0xb9, 0x99, 0x8a, 0x99, 0x9e, 0x21,
            0xdb, 0x32, 0xdd, 0x97, 0x49, 0x6d, 0x33, 0x76
        }
    }
};

int main(int argc, char *argv[]) {
    printf("=== SHA3-256 Final Implementation Test ===\n\n");

    // Generate SHA3-256 circuit
    printf("Generating SHA3-256 circuit...\n");
    circuit_t *circuit = generate_sha3_circuit(SHA3_256);
    if (!circuit) {
        fprintf(stderr, "Failed to generate SHA3-256 circuit\n");
        return 1;
    }
    
    printf("SHA3-256 circuit generated successfully with %u gates and %u layers\n", 
        circuit->num_gates, circuit->num_layers);
    
    // Test against NIST test vectors
    printf("\nTesting against NIST test vectors:\n");
    
    for (size_t i = 0; i < sizeof(test_vectors) / sizeof(test_vectors[0]); i++) {
        const test_vector_t *vector = &test_vectors[i];
        
        printf("\nTest vector %zu: ", i + 1);
        if (vector->message_len <= 16) {
            printf("\"%s\" (length: %zu)\n", vector->message, vector->message_len);
        } else {
            printf("(length: %zu)\n", vector->message_len);
            printf("  Input: \"%.16s...\" (truncated)\n", vector->message);
        }
        
        // Calculate hash
        uint8_t output[32];
        if (!evaluate_sha3_circuit(circuit, (const uint8_t*)vector->message, vector->message_len, output)) {
            fprintf(stderr, "Failed to evaluate SHA3-256 circuit\n");
            evaluator_free_circuit(circuit);
            return 1;
        }
        
        // Print expected hash
        printf("  Expected: ");
        for (int j = 0; j < 32; j++) {
            printf("%02x", vector->hash[j]);
            if ((j + 1) % 4 == 0) printf(" ");
        }
        printf("\n");
        
        // Print calculated hash
        printf("  Actual:   ");
        for (int j = 0; j < 32; j++) {
            printf("%02x", output[j]);
            if ((j + 1) % 4 == 0) printf(" ");
        }
        printf("\n");
        
        // Check if hashes match
        bool match = memcmp(output, vector->hash, 32) == 0;
        printf("  Result:   %s\n", match ? "PASS" : "FAIL");
        
        if (!match) {
            printf("  Hash verification failed!\n");
            evaluator_free_circuit(circuit);
            return 1;
        }
    }
    
    printf("\nAll test vectors passed!\n");
    
    // Custom input test if provided
    if (argc > 1) {
        const char *custom_input = argv[1];
        size_t custom_len = strlen(custom_input);
        
        printf("\nTesting with custom input: \"%s\" (length: %zu)\n", custom_input, custom_len);
        
        // Calculate hash
        uint8_t output[32];
        if (!evaluate_sha3_circuit(circuit, (const uint8_t*)custom_input, custom_len, output)) {
            fprintf(stderr, "Failed to evaluate SHA3-256 circuit\n");
            evaluator_free_circuit(circuit);
            return 1;
        }
        
        // Print calculated hash
        printf("  SHA3-256: ");
        for (int j = 0; j < 32; j++) {
            printf("%02x", output[j]);
            if ((j + 1) % 4 == 0) printf(" ");
        }
        printf("\n");
    }
    
    evaluator_free_circuit(circuit);
    return 0;
}