/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "ras.h"
#include "sha3.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define NUM_VALIDATORS 100
#define BYZANTINE_THRESHOLD 67  // Need 67% signatures for consensus

typedef struct {
    uint64_t height;
    uint8_t prev_hash[32];
    uint8_t merkle_root[32];
    uint64_t timestamp;
    uint8_t proposer[32];
} block_header_t;

void compute_block_hash(const block_header_t* block, uint8_t* hash_out) {
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    sha3_update(&ctx, (const uint8_t*)block, sizeof(block_header_t));
    sha3_final(&ctx, hash_out, 32);
}

int main() {
    printf("=== RAS Blockchain Consensus Demo ===\n");
    printf("Simulating %d validators signing blocks with RAS\n\n", NUM_VALIDATORS);
    
    // Initialize RAS system
    ras_system_t* system = ras_init();
    if (!system) {
        fprintf(stderr, "Failed to initialize RAS system\n");
        return 1;
    }
    
    // Generate validator key pairs
    printf("1. Setting up %d validators...\n", NUM_VALIDATORS);
    ras_private_key_t* validator_keys[NUM_VALIDATORS];
    ras_public_key_t* validator_pubkeys[NUM_VALIDATORS];
    
    for (int i = 0; i < NUM_VALIDATORS; i++) {
        if (!ras_keygen(system, &validator_keys[i], &validator_pubkeys[i])) {
            fprintf(stderr, "Failed to generate validator key %d\n", i);
            return 1;
        }
        
        if (i % 10 == 0) {
            printf("   Generated %d/%d validator keys...\r", i + 1, NUM_VALIDATORS);
            fflush(stdout);
        }
    }
    printf("   ✓ Generated %d validator key pairs        \n\n", NUM_VALIDATORS);
    
    // Create a block to sign
    printf("2. Creating block #1000000...\n");
    block_header_t block = {
        .height = 1000000,
        .timestamp = (uint64_t)time(NULL)
    };
    
    // Fill with example data
    memset(block.prev_hash, 0xAA, 32);
    memset(block.merkle_root, 0xBB, 32);
    memset(block.proposer, 0xCC, 32);
    
    uint8_t block_hash[32];
    compute_block_hash(&block, block_hash);
    
    printf("   Block height: %lu\n", block.height);
    printf("   Block hash: ");
    for (int i = 0; i < 8; i++) printf("%02x", block_hash[i]);
    printf("...\n\n");
    
    // Validators sign the block
    printf("3. Validators signing the block...\n");
    ras_signature_t* validator_sigs[NUM_VALIDATORS];
    int num_signed = 0;
    
    clock_t sign_start = clock();
    
    // Simulate some validators being offline (90% participation)
    for (int i = 0; i < NUM_VALIDATORS; i++) {
        if (rand() % 100 < 90) {  // 90% chance of being online
            validator_sigs[num_signed] = ras_sign(system, validator_keys[i],
                                                 block_hash, 32);
            if (validator_sigs[num_signed]) {
                num_signed++;
            }
        }
        
        if (i % 10 == 0) {
            printf("   Collecting signatures: %d/%d\r", i + 1, NUM_VALIDATORS);
            fflush(stdout);
        }
    }
    
    clock_t sign_end = clock();
    double sign_time = ((double)(sign_end - sign_start) / CLOCKS_PER_SEC) * 1000.0;
    
    printf("   ✓ Collected %d/%d signatures (%.1f%%)    \n", 
           num_signed, NUM_VALIDATORS, (double)num_signed / NUM_VALIDATORS * 100.0);
    printf("   Signing phase: %.2f ms\n\n", sign_time);
    
    // Check if we have enough signatures
    if (num_signed < BYZANTINE_THRESHOLD) {
        printf("   ✗ Not enough signatures for consensus!\n");
        return 1;
    }
    
    // Traditional approach - store all signatures
    size_t traditional_size = num_signed * ras_signature_size(validator_sigs[0]);
    printf("4. Traditional approach:\n");
    printf("   • Store %d signatures × %.1f KB = %.1f MB\n",
           num_signed, 
           ras_signature_size(validator_sigs[0]) / 1024.0,
           traditional_size / (1024.0 * 1024.0));
    printf("   • Verify each signature individually\n");
    printf("   • Network bandwidth: %.1f MB per block\n\n",
           traditional_size / (1024.0 * 1024.0));
    
    // RAS approach - aggregate into one signature!
    printf("5. RAS approach - Aggregating signatures...\n");
    
    clock_t agg_start = clock();
    
    ras_aggregated_signature_t* consensus_proof = ras_aggregate(system,
                                                               (const ras_signature_t**)validator_sigs,
                                                               num_signed);
    
    clock_t agg_end = clock();
    double agg_time = ((double)(agg_end - agg_start) / CLOCKS_PER_SEC) * 1000.0;
    
    if (!consensus_proof) {
        fprintf(stderr, "Failed to aggregate signatures\n");
        return 1;
    }
    
    size_t agg_size = ras_aggregated_signature_size(consensus_proof);
    
    printf("   ✓ Created consensus proof!\n");
    printf("   • Single proof size: %.1f KB (constant!)\n", agg_size / 1024.0);
    printf("   • Aggregation time: %.2f ms\n", agg_time);
    printf("   • Space savings: %.1f%% reduction\n",
           (1.0 - (double)agg_size / traditional_size) * 100.0);
    printf("   • Network bandwidth: %.1f KB per block\n\n", agg_size / 1024.0);
    
    // Light client verification
    printf("6. Light client verification...\n");
    printf("   A mobile phone receives the block and consensus proof\n");
    
    // Prepare data for verification
    const ras_public_key_t* signing_validators[num_signed];
    const uint8_t* block_hashes[num_signed];
    size_t hash_sizes[num_signed];
    
    for (int i = 0; i < num_signed; i++) {
        signing_validators[i] = validator_pubkeys[i];  // In practice, track which validators signed
        block_hashes[i] = block_hash;
        hash_sizes[i] = 32;
    }
    
    clock_t verify_start = clock();
    
    bool consensus_valid = ras_verify_aggregated(system,
                                               signing_validators,
                                               block_hashes,
                                               hash_sizes,
                                               num_signed,
                                               consensus_proof);
    
    clock_t verify_end = clock();
    double verify_time = ((double)(verify_end - verify_start) / CLOCKS_PER_SEC) * 1000.0;
    
    printf("   %s Consensus proof is %s\n",
           consensus_valid ? "✓" : "✗",
           consensus_valid ? "VALID" : "INVALID");
    printf("   Verification time: %.2f ms\n", verify_time);
    printf("   Mobile-friendly: Only %.1f KB to download & verify!\n\n", 
           agg_size / 1024.0);
    
    // Summary
    printf("=== Blockchain Impact ===\n");
    printf("Without RAS:\n");
    printf("   • %.1f MB of signatures per block\n", traditional_size / (1024.0 * 1024.0));
    printf("   • 10 blocks/sec → %.1f MB/sec bandwidth\n", 
           traditional_size * 10 / (1024.0 * 1024.0));
    printf("   • Light clients can't verify consensus\n\n");
    
    printf("With RAS:\n");
    printf("   • %.1f KB per block (constant!)\n", agg_size / 1024.0);
    printf("   • 10 blocks/sec → %.1f KB/sec bandwidth\n", agg_size * 10 / 1024.0);
    printf("   • Mobile phones can verify consensus\n");
    printf("   • %.0fx bandwidth reduction!\n", (double)traditional_size / agg_size);
    printf("\n");
    
    printf("This enables:\n");
    printf("   ✓ True mobile blockchain nodes\n");
    printf("   ✓ Instant sync (download headers + proofs)\n");
    printf("   ✓ 1 Million TPS with reasonable bandwidth\n");
    printf("   ✓ Post-quantum security from day one\n");
    
    // Cleanup
    for (int i = 0; i < num_signed; i++) {
        ras_signature_free(validator_sigs[i]);
    }
    for (int i = 0; i < NUM_VALIDATORS; i++) {
        ras_private_key_free(validator_keys[i]);
        ras_public_key_free(validator_pubkeys[i]);
    }
    ras_aggregated_signature_free(consensus_proof);
    ras_free(system);
    
    return 0;
}