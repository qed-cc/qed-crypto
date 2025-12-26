/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "ras.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define NUM_SIGNERS 10

int main() {
    printf("=== RAS Aggregation Demo ===\n");
    printf("Demonstrating the power of Recursive Aggregatable Signatures\n\n");
    
    // Initialize RAS system
    ras_system_t* system = ras_init();
    if (!system) {
        fprintf(stderr, "Failed to initialize RAS system\n");
        return 1;
    }
    
    // Generate multiple key pairs
    printf("1. Generating %d key pairs...\n", NUM_SIGNERS);
    ras_private_key_t* private_keys[NUM_SIGNERS];
    ras_public_key_t* public_keys[NUM_SIGNERS];
    
    for (int i = 0; i < NUM_SIGNERS; i++) {
        if (!ras_keygen(system, &private_keys[i], &public_keys[i])) {
            fprintf(stderr, "Failed to generate key pair %d\n", i);
            return 1;
        }
    }
    printf("   ✓ Generated %d key pairs\n\n", NUM_SIGNERS);
    
    // Each signer signs a different message
    printf("2. Creating %d signatures on different messages...\n", NUM_SIGNERS);
    ras_signature_t* signatures[NUM_SIGNERS];
    char messages[NUM_SIGNERS][100];
    
    clock_t sign_start = clock();
    
    for (int i = 0; i < NUM_SIGNERS; i++) {
        snprintf(messages[i], sizeof(messages[i]), 
                 "Transaction #%d from wallet 0x%04x", i, i * 1337);
        
        signatures[i] = ras_sign(system, private_keys[i],
                               (const uint8_t*)messages[i],
                               strlen(messages[i]));
        
        if (!signatures[i]) {
            fprintf(stderr, "Failed to create signature %d\n", i);
            return 1;
        }
        
        printf("   Signed: \"%s\"\n", messages[i]);
    }
    
    clock_t sign_end = clock();
    double total_sign_time = ((double)(sign_end - sign_start) / CLOCKS_PER_SEC) * 1000.0;
    
    size_t individual_size = ras_signature_size(signatures[0]);
    size_t total_individual_size = individual_size * NUM_SIGNERS;
    
    printf("\n   ✓ Created %d signatures\n", NUM_SIGNERS);
    printf("   Total signing time: %.2f ms\n", total_sign_time);
    printf("   Individual signature size: %.1f KB\n", individual_size / 1024.0);
    printf("   Total size (traditional): %.1f KB\n\n", total_individual_size / 1024.0);
    
    // THE MAGIC: Aggregate all signatures into ONE
    printf("3. Aggregating %d signatures into ONE proof...\n", NUM_SIGNERS);
    
    clock_t agg_start = clock();
    
    ras_aggregated_signature_t* agg_sig = ras_aggregate(system, 
                                                       (const ras_signature_t**)signatures,
                                                       NUM_SIGNERS);
    
    clock_t agg_end = clock();
    double agg_time = ((double)(agg_end - agg_start) / CLOCKS_PER_SEC) * 1000.0;
    
    if (!agg_sig) {
        fprintf(stderr, "Failed to aggregate signatures\n");
        return 1;
    }
    
    size_t agg_size = ras_aggregated_signature_size(agg_sig);
    
    printf("   ✓ Aggregated into single proof!\n");
    printf("   Aggregation time: %.2f ms\n", agg_time);
    printf("   Aggregated signature size: %.1f KB\n", agg_size / 1024.0);
    printf("   Space savings: %.1f%% reduction!\n\n", 
           (1.0 - (double)agg_size / total_individual_size) * 100.0);
    
    // Verify the aggregated signature
    printf("4. Verifying aggregated signature (all %d at once)...\n", NUM_SIGNERS);
    
    const uint8_t* msg_ptrs[NUM_SIGNERS];
    size_t msg_lens[NUM_SIGNERS];
    
    for (int i = 0; i < NUM_SIGNERS; i++) {
        msg_ptrs[i] = (const uint8_t*)messages[i];
        msg_lens[i] = strlen(messages[i]);
    }
    
    clock_t verify_start = clock();
    
    bool valid = ras_verify_aggregated(system,
                                      (const ras_public_key_t**)public_keys,
                                      msg_ptrs, msg_lens, NUM_SIGNERS,
                                      agg_sig);
    
    clock_t verify_end = clock();
    double verify_time = ((double)(verify_end - verify_start) / CLOCKS_PER_SEC) * 1000.0;
    
    printf("   %s All signatures are %s\n", 
           valid ? "✓" : "✗",
           valid ? "VALID" : "INVALID");
    printf("   Verification time: %.2f ms\n\n", verify_time);
    
    // Compare with individual verification
    printf("5. Comparing with individual verification...\n");
    
    clock_t ind_verify_start = clock();
    
    for (int i = 0; i < NUM_SIGNERS; i++) {
        bool ind_valid = ras_verify(system, public_keys[i],
                                   (const uint8_t*)messages[i],
                                   strlen(messages[i]),
                                   signatures[i]);
        if (!ind_valid) {
            printf("   ✗ Signature %d is INVALID\n", i);
        }
    }
    
    clock_t ind_verify_end = clock();
    double ind_verify_time = ((double)(ind_verify_end - ind_verify_start) / CLOCKS_PER_SEC) * 1000.0;
    
    printf("   Individual verification time: %.2f ms\n", ind_verify_time);
    printf("   Speedup: %.1fx faster with aggregation!\n\n", 
           ind_verify_time / verify_time);
    
    // Summary
    printf("=== Summary ===\n");
    printf("Traditional approach:\n");
    printf("   • %d signatures × %.1f KB = %.1f KB total\n", 
           NUM_SIGNERS, individual_size / 1024.0, total_individual_size / 1024.0);
    printf("   • Verify time: %.2f ms (%.2f ms per signature)\n",
           ind_verify_time, ind_verify_time / NUM_SIGNERS);
    printf("\n");
    printf("RAS approach:\n");
    printf("   • 1 aggregated signature = %.1f KB (constant!)\n", agg_size / 1024.0);
    printf("   • Verify time: %.2f ms (all %d at once!)\n", verify_time, NUM_SIGNERS);
    printf("\n");
    printf("Benefits:\n");
    printf("   • %.1f%% storage reduction\n", 
           (1.0 - (double)agg_size / total_individual_size) * 100.0);
    printf("   • %.1fx verification speedup\n", ind_verify_time / verify_time);
    printf("   • Post-quantum secure\n");
    printf("   • Perfect for blockchain consensus!\n");
    
    // Cleanup
    for (int i = 0; i < NUM_SIGNERS; i++) {
        ras_signature_free(signatures[i]);
        ras_private_key_free(private_keys[i]);
        ras_public_key_free(public_keys[i]);
    }
    ras_aggregated_signature_free(agg_sig);
    ras_free(system);
    
    return 0;
}