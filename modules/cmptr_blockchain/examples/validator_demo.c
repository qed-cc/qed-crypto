/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <cmptr_blockchain.h>
#include <validator.h>
#include <stdio.h>
#include <unistd.h>

int main(void) {
    printf("=== CMPTR Validator Node Demo ===\n\n");
    printf("Demonstrating ultra-lightweight validation\n\n");
    
    /* Initialize blockchain */
    blockchain_t* blockchain = cmptr_blockchain_init();
    if (!blockchain) {
        fprintf(stderr, "Failed to initialize blockchain\n");
        return 1;
    }
    
    /* Create validator node */
    printf("1. Creating validator node...\n");
    node_t* validator = cmptr_blockchain_create_validator(blockchain);
    if (!validator) {
        fprintf(stderr, "Failed to create validator\n");
        cmptr_blockchain_destroy(blockchain);
        return 1;
    }
    
    /* Show storage configuration */
    storage_config_t config = validator->storage_config;
    printf("   ✓ Validator created with ultra-light storage:\n");
    printf("   - Retention: %lu days\n", config.retention_days);
    printf("   - Store transactions: %s\n", config.store_transactions ? "Yes" : "No");
    printf("   - Store proofs: %s\n", config.store_proofs ? "Yes" : "No");
    printf("   - Max storage: %lu GB\n\n", config.max_storage_gb);
    
    /* Start validator */
    printf("2. Starting validator node...\n");
    if (!cmptr_blockchain_start_node(validator)) {
        fprintf(stderr, "Failed to start validator\n");
        cmptr_blockchain_destroy(blockchain);
        return 1;
    }
    printf("   ✓ Validator started on port %u\n\n", 
           validator->network_config.port);
    
    /* Simulate receiving blocks */
    printf("3. Simulating block validation:\n");
    
    for (int i = 0; i < 5; i++) {
        /* Create dummy block */
        block_t block = {0};
        block.height = i + 1;
        block.timestamp = time(NULL) * 1000000;
        block.producer_id = i % 10;
        block.difficulty = 20;
        block.tx_count = 100000;  /* 100k transactions */
        
        printf("   → Validating block #%lu...", block.height);
        fflush(stdout);
        
        /* Validate block */
        validator_t* val = &validator->data.validator;
        val->last_validated_height = i;  /* Simulate proper sequence */
        
        if (validator_validate_block(validator, &block)) {
            printf(" ✓ Valid\n");
        } else {
            printf(" ✗ Invalid\n");
        }
        
        sleep(1);
    }
    
    /* Show validator statistics */
    validator_t* val = &validator->data.validator;
    printf("\n4. Validator Statistics:\n");
    printf("   - Blocks validated: %lu\n", val->blocks_validated);
    printf("   - Last validated height: %lu\n", val->last_validated_height);
    printf("   - Storage used: ~%lu KB (headers only)\n", 
           val->last_validated_height * 1);  /* 1KB per header */
    
    /* Demonstrate fast sync */
    printf("\n5. Demonstrating validator fast sync:\n");
    
    /* Simulate accumulator proof */
    uint8_t fake_proof[32] = "ACCUMULATOR_ROOT_AT_HEIGHT_1000";
    if (validator_fast_sync(validator, fake_proof, 32, 1000)) {
        printf("   ✓ Fast synced to height 1000\n");
        printf("   - New validated height: %lu\n", val->last_validated_height);
        printf("   - Accumulator root: ");
        for (int i = 0; i < 8; i++) {
            printf("%02x", val->accumulator_root[i]);
        }
        printf("...\n");
    }
    
    /* Demonstrate state proof */
    printf("\n6. Getting validator state proof:\n");
    uint8_t state_proof[1024];
    size_t proof_size = 0;
    
    if (validator_get_state_proof(validator, state_proof, &proof_size)) {
        printf("   ✓ State proof generated (%zu bytes)\n", proof_size);
        printf("   - Can be used by light clients to verify state\n");
    }
    
    /* Show advantages */
    printf("\n7. Validator Node Advantages:\n");
    printf("   • Runs on mobile devices (< 1GB storage)\n");
    printf("   • Instant sync with accumulator proofs\n");
    printf("   • Full security without full data\n");
    printf("   • Perfect for IoT and edge devices\n");
    
    /* Compare to traditional nodes */
    printf("\n8. Storage Comparison:\n");
    printf("   Bitcoin full node:    ~550 GB\n");
    printf("   Ethereum full node:   ~1.2 TB\n");
    printf("   CMPTR validator:      ~1 GB (headers only)\n");
    printf("   CMPTR with proofs:    ~3.2 GB (bounded forever)\n");
    
    /* Cleanup */
    cmptr_blockchain_stop_node(validator);
    cmptr_blockchain_destroy(blockchain);
    
    printf("\n=== Demo Complete ===\n");
    printf("\nCMPTR validators enable true decentralization by allowing\n");
    printf("anyone to verify the blockchain on resource-constrained devices.\n");
    
    return 0;
}