/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <cmptr_blockchain.h>
#include <cmptr_accumulator.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>

static volatile bool running = true;

void signal_handler(int sig) {
    printf("\nShutting down...\n");
    running = false;
}

int main(void) {
    signal(SIGINT, signal_handler);
    
    printf("=== CMPTR Blockchain Demo ===\n\n");
    printf("Demonstrating hierarchical architecture for 1M TPS\n\n");
    
    /* Initialize blockchain */
    blockchain_t* blockchain = cmptr_blockchain_init();
    if (!blockchain) {
        fprintf(stderr, "Failed to initialize blockchain\n");
        return 1;
    }
    
    printf("1. Blockchain initialized with genesis block\n\n");
    
    /* Create hierarchical node structure */
    printf("2. Creating hierarchical node network:\n");
    
    /* Create 3 aggregators (representing 1000 total) */
    node_t* aggregators[3];
    for (int i = 0; i < 3; i++) {
        aggregators[i] = cmptr_blockchain_create_aggregator(blockchain, i);
        if (!cmptr_blockchain_start_node(aggregators[i])) {
            fprintf(stderr, "Failed to start aggregator %d\n", i);
        }
    }
    printf("   ✓ Created 3 aggregators (representing 1000 total)\n");
    
    /* Create 1 generator (representing 100 total) */
    node_t* generator = cmptr_blockchain_create_generator(blockchain, 0, 0);
    if (!cmptr_blockchain_start_node(generator)) {
        fprintf(stderr, "Failed to start generator\n");
    }
    printf("   ✓ Created 1 generator (representing 100 total)\n");
    
    /* Create 1 producer (representing 10 total) */
    node_t* producer = cmptr_blockchain_create_producer(blockchain, 0, 0);
    if (!cmptr_blockchain_start_node(producer)) {
        fprintf(stderr, "Failed to start producer\n");
    }
    printf("   ✓ Created 1 producer (representing 10 total)\n");
    
    /* Create 2 validators */
    node_t* validator1 = cmptr_blockchain_create_validator(blockchain);
    node_t* validator2 = cmptr_blockchain_create_validator(blockchain);
    if (!cmptr_blockchain_start_node(validator1) ||
        !cmptr_blockchain_start_node(validator2)) {
        fprintf(stderr, "Failed to start validators\n");
    }
    printf("   ✓ Created 2 validators\n\n");
    
    /* Simulate transaction flow */
    printf("3. Simulating transaction flow:\n");
    
    /* Create sample transactions */
    for (int i = 0; i < 10; i++) {
        transaction_t tx = {0};
        
        /* Generate random transaction data */
        for (int j = 0; j < 32; j++) {
            tx.id[j] = rand() & 0xFF;
            tx.nullifiers[0][j] = rand() & 0xFF;
            tx.nullifiers[1][j] = rand() & 0xFF;
            tx.commitments[0][j] = rand() & 0xFF;
            tx.commitments[1][j] = rand() & 0xFF;
        }
        tx.timestamp = time(NULL) * 1000000;
        tx.aggregator_id = i % 3;
        
        /* Submit to appropriate aggregator */
        if (cmptr_blockchain_submit_transaction(aggregators[i % 3], &tx)) {
            printf("   → Transaction %d submitted to Aggregator #%d\n", 
                   i, i % 3);
        }
    }
    
    printf("\n4. Network is running. Press Ctrl+C to stop.\n\n");
    
    /* Main loop - display metrics */
    int iteration = 0;
    while (running) {
        sleep(5);
        
        /* Get blockchain metrics */
        blockchain_metrics_t metrics = cmptr_blockchain_get_metrics(blockchain);
        
        printf("\r[%d] Height: %lu | TPS: %.1f | Transactions: %lu | Storage: %.2f GB",
               iteration++,
               metrics.blockchain_height,
               metrics.current_tps,
               metrics.total_transactions,
               metrics.storage_used_gb);
        fflush(stdout);
        
        /* Simulate more transactions periodically */
        if (iteration % 2 == 0) {
            for (int i = 0; i < 100; i++) {
                transaction_t tx = {0};
                for (int j = 0; j < 32; j++) {
                    tx.id[j] = rand() & 0xFF;
                }
                tx.timestamp = time(NULL) * 1000000;
                tx.aggregator_id = rand() % 3;
                
                cmptr_blockchain_submit_transaction(
                    aggregators[rand() % 3], &tx
                );
            }
        }
    }
    
    printf("\n\n5. Shutting down nodes...\n");
    
    /* Stop all nodes */
    for (int i = 0; i < 3; i++) {
        cmptr_blockchain_stop_node(aggregators[i]);
    }
    cmptr_blockchain_stop_node(generator);
    cmptr_blockchain_stop_node(producer);
    cmptr_blockchain_stop_node(validator1);
    cmptr_blockchain_stop_node(validator2);
    
    /* Final metrics */
    blockchain_metrics_t final_metrics = cmptr_blockchain_get_metrics(blockchain);
    printf("\n6. Final Statistics:\n");
    printf("   - Blockchain height: %lu\n", final_metrics.blockchain_height);
    printf("   - Total transactions: %lu\n", final_metrics.total_transactions);
    printf("   - Average TPS: %.1f\n", final_metrics.current_tps);
    printf("   - Storage used: %.2f GB\n", final_metrics.storage_used_gb);
    printf("   - Average block time: %.1f seconds\n", 
           final_metrics.avg_block_time_ms / 1000.0);
    
    /* Cleanup */
    cmptr_blockchain_destroy(blockchain);
    
    printf("\n=== Demo Complete ===\n");
    printf("\nThe CMPTR Blockchain demonstrates how hierarchical architecture\n");
    printf("enables 1 Million TPS while keeping storage bounded through\n");
    printf("integration with the CMPTR Accumulator's automatic pruning.\n");
    
    return 0;
}