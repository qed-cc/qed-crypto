#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include "circuit_engine.h"

// Test vectors from NIST
const char* test_inputs[] = {
    "", 
    "abc",
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
};

const char* expected_outputs_hex[] = {
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
    "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
};

// Helper to convert hex string to binary
static void hex_to_bin(const char* hex, uint8_t* bin, size_t bin_size) {
    size_t i;
    for (i = 0; i < bin_size; i++) {
        sscanf(hex + (i * 2), "%2hhx", &bin[i]);
    }
}

// Helper to print binary as hex
static void print_hex(const uint8_t* data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        printf("%02x", data[i]);
    }
    printf("\n");
}

int main() {
    printf("Testing circuit_sha3_engine implementation...\n");
    
    // Create SHA3-256 circuit
    circuit_t* circuit = generate_sha3_circuit(SHA3_256);
    if (!circuit) {
        fprintf(stderr, "Failed to generate SHA3-256 circuit\n");
        return 1;
    }
    
    // Test with each vector
    int test_count = sizeof(test_inputs) / sizeof(test_inputs[0]);
    int passed = 0;
    
    for (int i = 0; i < test_count; i++) {
        uint8_t output[32] = {0};
        uint8_t expected[32] = {0};
        
        // Get the expected output
        hex_to_bin(expected_outputs_hex[i], expected, 32);
        
        // Hash the input
        if (!evaluate_sha3_circuit(circuit, 
                           (const uint8_t*)test_inputs[i], 
                           strlen(test_inputs[i]), 
                           output)) {
            fprintf(stderr, "Failed to evaluate SHA3-256 circuit on input %d\n", i);
            return 1;
        }
        
        // Compare results
        if (memcmp(output, expected, 32) == 0) {
            printf("Test %d: PASSED\n", i);
            passed++;
        } else {
            printf("Test %d: FAILED\n", i);
            printf("  Input:    '%s'\n", test_inputs[i]);
            printf("  Expected: ");
            print_hex(expected, 32);
            printf("  Got:      ");
            print_hex(output, 32);
        }
    }
    
    // Free the circuit
    free(circuit);
    
    // Print summary
    printf("\nSummary: %d/%d tests passed\n", passed, test_count);
    
    return (passed == test_count) ? 0 : 1;
}