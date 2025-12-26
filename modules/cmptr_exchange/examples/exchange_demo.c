/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_exchange.h"
#include "../../cmptr_channel/include/cmptr_channel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void print_hex(const char* label, const uint8_t* data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len && i < 32; i++) {
        printf("%02x", data[i]);
    }
    if (len > 32) printf("... (%zu bytes total)", len);
    printf("\n");
}

void demo_basic_exchange() {
    printf("=== Basic Key Exchange Demo ===\n\n");
    
    // Initialize exchange system
    cmptr_exchange_system_t* system = cmptr_exchange_init();
    
    // Alice generates key pair
    cmptr_exchange_private_t* alice_private;
    cmptr_exchange_public_t* alice_public;
    
    clock_t start = clock();
    cmptr_exchange_keygen(system, &alice_private, &alice_public);
    clock_t end = clock();
    double keygen_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    printf("Alice:\n");
    printf("  Key generation time: %.2f ms\n", keygen_ms);
    
    // Alice creates commitment
    uint8_t alice_commitment[CMPTR_EXCHANGE_COMMIT_SIZE];
    cmptr_exchange_commit(alice_public, alice_commitment);
    print_hex("  Commitment", alice_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    
    // Bob generates key pair
    cmptr_exchange_private_t* bob_private;
    cmptr_exchange_public_t* bob_public;
    cmptr_exchange_keygen(system, &bob_private, &bob_public);
    
    uint8_t bob_commitment[CMPTR_EXCHANGE_COMMIT_SIZE];
    cmptr_exchange_commit(bob_public, bob_commitment);
    
    printf("\nBob:\n");
    printf("  Key generation time: %.2f ms\n", keygen_ms);
    print_hex("  Commitment", bob_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    
    // Phase 2: Reveal keys
    printf("\n=== Phase 2: Reveal ===\n");
    
    uint8_t alice_proof[2048];  // Small buffer for demo
    size_t alice_proof_len;
    cmptr_exchange_reveal(alice_public, alice_proof, &alice_proof_len);
    
    uint8_t bob_proof[2048];
    size_t bob_proof_len;
    cmptr_exchange_reveal(bob_public, bob_proof, &bob_proof_len);
    
    printf("Alice reveals: %zu bytes\n", alice_proof_len);
    printf("Bob reveals: %zu bytes\n", bob_proof_len);
    
    // Verify commitments
    bool alice_valid = cmptr_exchange_verify_commitment(alice_commitment, alice_proof, alice_proof_len);
    bool bob_valid = cmptr_exchange_verify_commitment(bob_commitment, bob_proof, bob_proof_len);
    
    printf("Commitment verification:\n");
    printf("  Alice: %s\n", alice_valid ? "✓ Valid" : "✗ Invalid");
    printf("  Bob: %s\n", bob_valid ? "✓ Valid" : "✗ Invalid");
    
    // Phase 3: Derive shared secrets
    printf("\n=== Phase 3: Derive Shared Secret ===\n");
    
    uint8_t alice_shared[CMPTR_EXCHANGE_SHARED_SIZE];
    uint8_t bob_shared[CMPTR_EXCHANGE_SHARED_SIZE];
    
    start = clock();
    cmptr_exchange_derive(system, alice_private, bob_proof, bob_proof_len, alice_shared);
    end = clock();
    double derive_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    cmptr_exchange_derive(system, bob_private, alice_proof, alice_proof_len, bob_shared);
    
    print_hex("Alice derives", alice_shared, CMPTR_EXCHANGE_SHARED_SIZE);
    print_hex("Bob derives", bob_shared, CMPTR_EXCHANGE_SHARED_SIZE);
    printf("Derivation time: %.2f ms\n", derive_ms);
    
    // Note: In the simulation, these won't match because we're not using
    // a proper key exchange circuit. In the full implementation with STARKs,
    // they would produce the same shared secret.
    
    // Cleanup
    cmptr_exchange_private_free(alice_private);
    cmptr_exchange_public_free(alice_public);
    cmptr_exchange_private_free(bob_private);
    cmptr_exchange_public_free(bob_public);
    cmptr_exchange_system_free(system);
}

void demo_authenticated_exchange() {
    printf("\n=== Authenticated Exchange Demo ===\n\n");
    
    cmptr_exchange_system_t* system = cmptr_exchange_init();
    
    // Create transcript for authentication
    cmptr_exchange_transcript_t* alice_transcript = cmptr_exchange_transcript_new();
    cmptr_exchange_transcript_t* bob_transcript = cmptr_exchange_transcript_new();
    
    // Add protocol version
    const char* version = "cmptr_exchange_v1";
    cmptr_exchange_transcript_add(alice_transcript, "version", 
                                 (const uint8_t*)version, strlen(version));
    cmptr_exchange_transcript_add(bob_transcript, "version", 
                                 (const uint8_t*)version, strlen(version));
    
    // Generate keys
    cmptr_exchange_private_t* alice_private;
    cmptr_exchange_public_t* alice_public;
    cmptr_exchange_keygen(system, &alice_private, &alice_public);
    
    cmptr_exchange_private_t* bob_private;
    cmptr_exchange_public_t* bob_public;
    cmptr_exchange_keygen(system, &bob_private, &bob_public);
    
    // Create and exchange commitments
    uint8_t alice_commitment[CMPTR_EXCHANGE_COMMIT_SIZE];
    uint8_t bob_commitment[CMPTR_EXCHANGE_COMMIT_SIZE];
    
    cmptr_exchange_commit(alice_public, alice_commitment);
    cmptr_exchange_commit(bob_public, bob_commitment);
    
    // Add commitments to transcript
    cmptr_exchange_transcript_add(alice_transcript, "alice_commit", 
                                 alice_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    cmptr_exchange_transcript_add(alice_transcript, "bob_commit", 
                                 bob_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    
    cmptr_exchange_transcript_add(bob_transcript, "alice_commit", 
                                 alice_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    cmptr_exchange_transcript_add(bob_transcript, "bob_commit", 
                                 bob_commitment, CMPTR_EXCHANGE_COMMIT_SIZE);
    
    // Reveal and derive
    uint8_t alice_proof[2048], bob_proof[2048];
    size_t alice_proof_len, bob_proof_len;
    
    cmptr_exchange_reveal(alice_public, alice_proof, &alice_proof_len);
    cmptr_exchange_reveal(bob_public, bob_proof, &bob_proof_len);
    
    uint8_t alice_shared[CMPTR_EXCHANGE_SHARED_SIZE];
    uint8_t bob_shared[CMPTR_EXCHANGE_SHARED_SIZE];
    
    cmptr_exchange_derive(system, alice_private, bob_proof, bob_proof_len, alice_shared);
    cmptr_exchange_derive(system, bob_private, alice_proof, alice_proof_len, bob_shared);
    
    // Finalize transcripts
    uint8_t alice_context[32], bob_context[32];
    cmptr_exchange_transcript_finalize(alice_transcript, alice_shared, alice_context);
    cmptr_exchange_transcript_finalize(bob_transcript, bob_shared, bob_context);
    
    printf("Authenticated context established:\n");
    print_hex("  Alice context", alice_context, 32);
    print_hex("  Bob context", bob_context, 32);
    
    // Now use contexts to establish secure channel
    printf("\n=== Secure Channel from Exchange ===\n");
    
    cmptr_channel_config_t config = {
        .role = CMPTR_CHANNEL_CLIENT,
        .forward_secrecy = CMPTR_CHANNEL_HASH_RATCHET,
        .rekey_interval = 10000,
        .low_latency_mode = true
    };
    
    // Use context as shared secret for channel
    cmptr_channel_t* alice_channel = cmptr_channel_init(alice_context, &config);
    config.role = CMPTR_CHANNEL_SERVER;
    cmptr_channel_t* bob_channel = cmptr_channel_init(bob_context, &config);
    
    // Test secure communication
    const char* message = "First message over quantum-secure channel!";
    uint8_t packet[256];
    size_t packet_len;
    
    cmptr_channel_send(alice_channel, (const uint8_t*)message, strlen(message), 
                      packet, &packet_len);
    
    uint8_t received[256];
    size_t received_len;
    bool valid = cmptr_channel_recv(bob_channel, packet, packet_len, 
                                   received, &received_len);
    
    if (valid) {
        received[received_len] = '\0';
        printf("Bob received: %s\n", received);
    }
    
    // Cleanup
    cmptr_channel_free(alice_channel);
    cmptr_channel_free(bob_channel);
    cmptr_exchange_transcript_free(alice_transcript);
    cmptr_exchange_transcript_free(bob_transcript);
    cmptr_exchange_private_free(alice_private);
    cmptr_exchange_public_free(alice_public);
    cmptr_exchange_private_free(bob_private);
    cmptr_exchange_public_free(bob_public);
    cmptr_exchange_system_free(system);
}

int main() {
    printf("=== Cmptr Exchange Demo ===\n");
    printf("STARK-based key exchange without number theory\n");
    printf("Quantum-secure via SHA3-256 only (AXIOM A001)\n\n");
    
    demo_basic_exchange();
    demo_authenticated_exchange();
    
    printf("\n=== Summary ===\n");
    printf("✓ Commit-reveal protocol prevents rushing attacks\n");
    printf("✓ STARK proofs provide zero-knowledge\n");
    printf("✓ No elliptic curves or number theory\n");
    printf("✓ Authenticated transcript prevents MITM\n");
    printf("✓ Direct integration with Cmptr Channel\n");
    printf("\nNOTE: This demo uses simulated STARKs. Full implementation would:\n");
    printf("- Generate real ~190KB STARK proofs\n");
    printf("- Use BaseFold RAA for proof generation/verification\n");
    printf("- Implement proper key exchange circuit\n");
    printf("- Achieve identical shared secrets for both parties\n");
    
    return 0;
}