/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_trees.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void print_hex(const char* label, const uint8_t* data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len && i < 32; i++) {
        printf("%02x", data[i]);
    }
    if (len > 32) printf("...");
    printf("\n");
}

void demo_basic_merkle() {
    printf("=== Basic Merkle Tree Demo ===\n\n");
    
    // Create tree with default config
    cmptr_tree_config_t config = {
        .type = CMPTR_TREE_STANDARD,
        .optimization_flags = CMPTR_TREE_OPT_NONE,
        .cache_enabled = true
    };
    
    cmptr_tree_t* tree = cmptr_tree_new(&config);
    
    // Add some leaves
    const char* data[] = {
        "Transaction 1: Alice -> Bob: 100",
        "Transaction 2: Bob -> Carol: 50",
        "Transaction 3: Carol -> Dave: 25",
        "Transaction 4: Dave -> Eve: 12"
    };
    
    printf("Adding transactions to tree:\n");
    for (int i = 0; i < 4; i++) {
        clock_t start = clock();
        cmptr_tree_add(tree, (const uint8_t*)data[i], strlen(data[i]));
        clock_t end = clock();
        double ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        printf("  %d. %s (%.3f ms)\n", i+1, data[i], ms);
    }
    
    // Get root hash
    uint8_t root[CMPTR_TREE_HASH_SIZE];
    cmptr_tree_root(tree, root);
    printf("\nMerkle root: ");
    print_hex("", root, CMPTR_TREE_HASH_SIZE);
    
    // Generate and verify proof for transaction 2
    printf("\n=== Inclusion Proof ===\n");
    uint64_t prove_index = 1;  // Transaction 2
    
    clock_t start = clock();
    cmptr_tree_proof_t* proof = cmptr_tree_prove(tree, prove_index);
    clock_t end = clock();
    double prove_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    printf("Generated proof for: \"%s\"\n", data[prove_index]);
    printf("Proof generation time: %.3f ms\n", prove_ms);
    
    // Verify the proof
    start = clock();
    bool valid = cmptr_tree_verify(
        root, prove_index,
        (const uint8_t*)data[prove_index], strlen(data[prove_index]),
        proof
    );
    end = clock();
    double verify_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    printf("Verification result: %s (%.3f ms)\n", 
           valid ? "✓ Valid" : "✗ Invalid", verify_ms);
    
    // Show statistics
    cmptr_tree_stats_t stats;
    cmptr_tree_stats(tree, &stats);
    printf("\n=== Tree Statistics ===\n");
    printf("Leaf count: %lu\n", stats.leaf_count);
    printf("Hash computations: %lu\n", stats.hash_computations);
    printf("Memory usage: %zu bytes\n", stats.memory_usage);
    printf("Cache hit rate: %.1f%%\n", stats.cache_hit_rate * 100);
    
    cmptr_tree_proof_free(proof);
    cmptr_tree_free(tree);
}

void demo_batch_operations() {
    printf("\n\n=== Batch Operations Demo ===\n");
    printf("Efficient bulk insertion with AVX-512\n\n");
    
    cmptr_tree_config_t config = {
        .type = CMPTR_TREE_STANDARD,
        .optimization_flags = CMPTR_TREE_OPT_BATCH,
        .leaf_count_hint = 10000,
        .cache_enabled = true
    };
    
    cmptr_tree_t* tree = cmptr_tree_new(&config);
    cmptr_tree_batch_t* batch = cmptr_tree_batch_new(tree);
    
    // Prepare 1000 transactions
    printf("Preparing 1000 transactions...\n");
    char tx_buffer[128];
    
    for (int i = 0; i < 1000; i++) {
        snprintf(tx_buffer, sizeof(tx_buffer), "TX_%06d: Random data %d", i, rand());
        cmptr_tree_batch_add(batch, (const uint8_t*)tx_buffer, strlen(tx_buffer));
    }
    
    // Commit batch
    printf("Committing batch...\n");
    clock_t start = clock();
    cmptr_tree_batch_commit(batch);
    clock_t end = clock();
    double batch_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    printf("Batch commit time: %.1f ms (%.3f ms per transaction)\n", 
           batch_ms, batch_ms / 1000);
    
    // Get final root
    uint8_t root[CMPTR_TREE_HASH_SIZE];
    cmptr_tree_root(tree, root);
    print_hex("Final root", root, CMPTR_TREE_HASH_SIZE);
    
    // Statistics
    cmptr_tree_stats_t stats;
    cmptr_tree_stats(tree, &stats);
    printf("\nBatch statistics:\n");
    printf("  Total leaves: %lu\n", stats.leaf_count);
    printf("  Hash computations: %lu\n", stats.hash_computations);
    printf("  Hashes per leaf: %.2f\n", (double)stats.hash_computations / stats.leaf_count);
    
    cmptr_tree_batch_free(batch);
    cmptr_tree_free(tree);
}

void demo_blockchain_use_case() {
    printf("\n\n=== Blockchain Block Validation Demo ===\n");
    printf("Using Merkle trees for transaction validation\n\n");
    
    // Simulate a blockchain block
    typedef struct {
        uint32_t block_height;
        uint8_t prev_hash[32];
        uint8_t tx_root[32];
        uint32_t tx_count;
        time_t timestamp;
    } block_header_t;
    
    // Create tree for transactions
    cmptr_tree_config_t config = {
        .type = CMPTR_TREE_STANDARD,
        .optimization_flags = CMPTR_TREE_OPT_VERIFY_SPEED,
        .cache_enabled = true
    };
    
    cmptr_tree_t* tx_tree = cmptr_tree_new(&config);
    
    // Simulate transactions in block
    const char* transactions[] = {
        "COINBASE: 12.5 BTC to miner",
        "Alice -> Bob: 1.5 BTC",
        "Bob -> Carol: 0.8 BTC", 
        "Carol -> Dave: 0.3 BTC",
        "Dave -> Eve: 0.1 BTC",
        "Fee: 0.001 BTC"
    };
    
    printf("Block #500,000 transactions:\n");
    for (size_t i = 0; i < sizeof(transactions)/sizeof(transactions[0]); i++) {
        cmptr_tree_add(tx_tree, (const uint8_t*)transactions[i], strlen(transactions[i]));
        printf("  %zu. %s\n", i+1, transactions[i]);
    }
    
    // Create block header
    block_header_t header = {
        .block_height = 500000,
        .tx_count = sizeof(transactions)/sizeof(transactions[0]),
        .timestamp = time(NULL)
    };
    
    // Set previous block hash (dummy)
    memset(header.prev_hash, 0xAB, 32);
    
    // Get transaction root
    cmptr_tree_root(tx_tree, header.tx_root);
    
    printf("\n=== Block Header ===\n");
    printf("Height: %u\n", header.block_height);
    print_hex("Previous", header.prev_hash, 32);
    print_hex("TX Root", header.tx_root, 32);
    printf("TX Count: %u\n", header.tx_count);
    printf("Timestamp: %ld\n", header.timestamp);
    
    // Light client verification
    printf("\n=== Light Client Verification ===\n");
    printf("Verifying transaction: \"%s\"\n", transactions[2]);
    
    cmptr_tree_proof_t* proof = cmptr_tree_prove(tx_tree, 2);
    
    // Simulate sending only header + proof to light client
    bool verified = cmptr_tree_verify(
        header.tx_root, 2,
        (const uint8_t*)transactions[2], strlen(transactions[2]),
        proof
    );
    
    printf("Light client verification: %s\n", verified ? "✓ Valid" : "✗ Invalid");
    printf("Data sent to light client:\n");
    printf("  Block header: %zu bytes\n", sizeof(header));
    printf("  Merkle proof: ~%u bytes\n", 32 * 6);  // Approximate
    printf("  Total: ~%zu bytes (vs %u full transactions)\n", 
           sizeof(header) + 32 * 6, header.tx_count);
    
    cmptr_tree_proof_free(proof);
    cmptr_tree_free(tx_tree);
}

void benchmark_performance() {
    printf("\n\n=== Performance Benchmark ===\n");
    printf("Comparing different optimization modes\n\n");
    
    struct {
        const char* name;
        uint32_t flags;
    } configs[] = {
        {"No optimization", CMPTR_TREE_OPT_NONE},
        {"Batch optimized", CMPTR_TREE_OPT_BATCH},
        {"Streaming optimized", CMPTR_TREE_OPT_STREAMING},
        {"Proof size optimized", CMPTR_TREE_OPT_PROOF_SIZE},
        {"Verify speed optimized", CMPTR_TREE_OPT_VERIFY_SPEED}
    };
    
    const int leaf_count = 10000;
    
    for (size_t i = 0; i < sizeof(configs)/sizeof(configs[0]); i++) {
        printf("\n--- %s ---\n", configs[i].name);
        
        cmptr_tree_config_t config = {
            .type = CMPTR_TREE_STANDARD,
            .optimization_flags = configs[i].flags,
            .leaf_count_hint = leaf_count,
            .cache_enabled = true
        };
        
        cmptr_tree_t* tree = cmptr_tree_new(&config);
        
        // Build tree
        clock_t start = clock();
        char data[64];
        for (int j = 0; j < leaf_count; j++) {
            snprintf(data, sizeof(data), "leaf_%d", j);
            cmptr_tree_add(tree, (const uint8_t*)data, strlen(data));
        }
        clock_t end = clock();
        double build_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        // Generate proofs
        start = clock();
        cmptr_tree_proof_t* proofs[100];
        for (int j = 0; j < 100; j++) {
            proofs[j] = cmptr_tree_prove(tree, rand() % leaf_count);
        }
        end = clock();
        double prove_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        // Verify proofs
        uint8_t root[CMPTR_TREE_HASH_SIZE];
        cmptr_tree_root(tree, root);
        
        start = clock();
        for (int j = 0; j < 100; j++) {
            snprintf(data, sizeof(data), "leaf_%lu", proofs[j]->leaf_index);
            cmptr_tree_verify(root, proofs[j]->leaf_index,
                            (const uint8_t*)data, strlen(data), proofs[j]);
        }
        end = clock();
        double verify_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        printf("  Build time: %.1f ms (%.3f μs/leaf)\n", 
               build_ms, build_ms * 1000 / leaf_count);
        printf("  Prove time: %.1f ms (%.2f ms/proof)\n",
               prove_ms, prove_ms / 100);
        printf("  Verify time: %.1f ms (%.2f ms/verify)\n",
               verify_ms, verify_ms / 100);
        
        cmptr_tree_stats_t stats;
        cmptr_tree_stats(tree, &stats);
        printf("  Cache hit rate: %.1f%%\n", stats.cache_hit_rate * 100);
        
        // Cleanup
        for (int j = 0; j < 100; j++) {
            cmptr_tree_proof_free(proofs[j]);
        }
        cmptr_tree_free(tree);
    }
}

int main() {
    printf("=== Cmptr Trees Demo ===\n");
    printf("Optimized Merkle trees with AVX-512 acceleration\n");
    printf("Quantum-secure via SHA3-256 only (AXIOM A001)\n\n");
    
    demo_basic_merkle();
    demo_batch_operations();
    demo_blockchain_use_case();
    benchmark_performance();
    
    printf("\n\n=== Summary ===\n");
    printf("✓ Standard and sparse Merkle tree support\n");
    printf("✓ AVX-512 batch hashing (when available)\n");
    printf("✓ Optimized for different use cases\n");
    printf("✓ Cache-friendly implementation\n");
    printf("✓ SHA3-only construction (quantum-secure)\n");
    printf("\nFuture enhancements:\n");
    printf("- Verkle tree mode for constant-size proofs\n");
    printf("- Multi-threaded batch operations\n");
    printf("- Persistent storage backend\n");
    printf("- Range proof optimization\n");
    
    return 0;
}