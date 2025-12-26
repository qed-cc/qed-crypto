/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "ras.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int main() {
    printf("=== RAS Basic Demo ===\n");
    printf("Recursive Aggregatable Signatures with STARKs\n\n");
    
    // Initialize RAS system
    ras_system_t* system = ras_init();
    if (!system) {
        fprintf(stderr, "Failed to initialize RAS system\n");
        return 1;
    }
    
    // Generate key pair
    printf("1. Generating key pair...\n");
    ras_private_key_t* private_key = NULL;
    ras_public_key_t* public_key = NULL;
    
    if (!ras_keygen(system, &private_key, &public_key)) {
        fprintf(stderr, "Failed to generate key pair\n");
        ras_free(system);
        return 1;
    }
    printf("   ✓ Key pair generated\n\n");
    
    // Sign a message
    const char* message = "Hello, Recursive Aggregatable Signatures!";
    printf("2. Signing message: \"%s\"\n", message);
    
    ras_signature_t* signature = ras_sign(system, private_key, 
                                         (const uint8_t*)message, 
                                         strlen(message));
    if (!signature) {
        fprintf(stderr, "Failed to sign message\n");
        ras_private_key_free(private_key);
        ras_public_key_free(public_key);
        ras_free(system);
        return 1;
    }
    
    size_t sig_size = ras_signature_size(signature);
    printf("   ✓ Signature created (size: %.1f KB)\n\n", sig_size / 1024.0);
    
    // Verify the signature
    printf("3. Verifying signature...\n");
    bool valid = ras_verify(system, public_key, 
                           (const uint8_t*)message, strlen(message),
                           signature);
    
    printf("   %s Signature is %s\n\n", 
           valid ? "✓" : "✗", 
           valid ? "VALID" : "INVALID");
    
    // Show metrics
    ras_metrics_t metrics = ras_get_metrics(system);
    printf("Performance Metrics:\n");
    printf("   Sign time: %.2f ms\n", metrics.sign_time_ms);
    printf("   Verify time: %.2f ms\n", metrics.verify_time_ms);
    printf("   Signature size: %.1f KB\n", metrics.signature_size_bytes / 1024.0);
    printf("\n");
    
    printf("Key Features:\n");
    printf("   • Post-quantum secure (no elliptic curves)\n");
    printf("   • Based on SHA3-256 only (AXIOM A001)\n");
    printf("   • Zero-knowledge by default (AXIOM A002)\n");
    printf("   • 121-bit security level\n");
    printf("   • Can aggregate multiple signatures into one!\n");
    
    // Cleanup
    ras_signature_free(signature);
    ras_private_key_free(private_key);
    ras_public_key_free(public_key);
    ras_free(system);
    
    return 0;
}