/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <cmptr_accumulator.h>
#include <block_structure.h>
#include <stdio.h>
#include <time.h>

int main(void) {
    printf("=== Gate Accumulator Mining Demo ===\n\n");
    
    /* Create genesis block */
    printf("1. Creating genesis block...\n");
    uint64_t genesis_time = time(NULL) * 1000000;
    block_t* genesis = create_genesis_block(genesis_time);
    
    print_block_header(&genesis->header);
    
    /* Mine first block */
    printf("\n2. Mining first block...\n");
    
    /* Create some transactions */
    uint8_t transactions[1000];
    for (int i = 0; i < 1000; i++) {
        transactions[i] = i & 0xFF;
    }
    
    block_t* block1 = create_block(genesis, transactions, 1000, time(NULL) * 1000000);
    
    /* Create mining context */
    mining_context_t* ctx = create_mining_context(
        genesis,
        block1->header.tx_merkle_root,
        block1->header.timestamp,
        20  /* difficulty */
    );
    
    printf("   Mining with %u threads...\n", 4);
    clock_t start = clock();
    
    /* Mine with 4 threads */
    mine_block_parallel(ctx, &block1->header, 4);
    
    clock_t end = clock();
    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
    
    if (ctx->solution_found) {
        printf("   Solution found in %.2f seconds!\n", elapsed);
        printf("   Nonce: ");
        for (int i = 0; i < 8; i++) printf("%02x", block1->header.nonce[i]);
        printf("...\n");
        printf("   Hash: ");
        for (int i = 0; i < 8; i++) printf("%02x", block1->header.pow_hash[i]);
        printf("...\n");
        printf("   Leading zeros: %u\n", count_leading_zeros(block1->header.pow_hash));
        
        double hash_rate = calculate_hash_rate(ctx->hashes_tried, elapsed * 1000000);
        printf("   Hash rate: %.2f MH/s\n", hash_rate / 1000000);
    }
    
    /* Validate block */
    printf("\n3. Validating block...\n");
    chain_state_t* chain = create_chain_state(genesis);
    block_validation_t validation = validate_block(block1, genesis, chain);
    
    printf("   Valid: %s\n", validation.valid ? "YES" : "NO");
    printf("   PoW valid: %s\n", validation.pow_valid ? "YES" : "NO");
    printf("   Timestamp valid: %s\n", validation.timestamp_valid ? "YES" : "NO");
    
    /* Difficulty adjustment */
    printf("\n4. Difficulty adjustment:\n");
    uint64_t target_time = 10 * 1000000;  /* 10 seconds */
    uint64_t actual_time = block1->header.timestamp - genesis->header.timestamp;
    
    uint32_t new_difficulty = calculate_next_difficulty(
        &block1->header,
        &genesis->header,
        target_time
    );
    
    printf("   Target block time: %.1f seconds\n", target_time / 1000000.0);
    printf("   Actual block time: %.1f seconds\n", actual_time / 1000000.0);
    printf("   Current difficulty: %u\n", block1->header.difficulty);
    printf("   Next difficulty: %u\n", new_difficulty);
    
    /* Show PoW security */
    printf("\n5. Proof of Work Security:\n");
    printf("   - SHA3-256 based (quantum resistant)\n");
    printf("   - Difficulty adjusts every block\n");
    printf("   - Parallel mining supported\n");
    printf("   - Timestamp validation prevents manipulation\n");
    
    /* Clean up */
    free(genesis->transactions);
    free(genesis);
    free(block1->transactions);
    free(block1);
    free(ctx);
    free(chain);
    
    printf("\n=== Demo Complete ===\n");
    return 0;
}