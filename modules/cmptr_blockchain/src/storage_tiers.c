/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>
#include <time.h>

/* Calculate storage required for node */
uint64_t calculate_storage_required(
    const node_t* node,
    uint64_t chain_height
) {
    if (!node) return 0;
    
    const storage_config_t* config = &node->storage_config;
    uint64_t storage_bytes = 0;
    
    /* Block headers: 1KB each */
    storage_bytes += chain_height * 1024;
    
    if (config->retention_days == 0) {
        /* Archive node - store everything */
        if (config->store_transactions) {
            /* ~100k transactions per block, 256 bytes each */
            storage_bytes += chain_height * 100000 * 256;
        }
        if (config->store_proofs) {
            /* 3 proofs per block, 190KB each */
            storage_bytes += chain_height * 3 * 190 * 1024;
        }
    } else {
        /* Limited retention */
        uint64_t blocks_per_day = (24 * 60 * 60) / 10;  /* 10 second blocks */
        uint64_t retained_blocks = blocks_per_day * config->retention_days;
        
        if (retained_blocks > chain_height) {
            retained_blocks = chain_height;
        }
        
        if (config->store_transactions) {
            storage_bytes += retained_blocks * 100000 * 256;
        }
        if (config->store_proofs) {
            storage_bytes += retained_blocks * 3 * 190 * 1024;
        }
    }
    
    return storage_bytes;
}

/* Prune old data based on retention policy */
uint64_t cmptr_blockchain_prune_old_data(node_t* node) {
    if (!node || !node->blockchain) return 0;
    
    const storage_config_t* config = &node->storage_config;
    
    if (config->retention_days == 0) {
        /* Archive node - never prune */
        return 0;
    }
    
    uint64_t current_time = time(NULL);
    uint64_t retention_seconds = config->retention_days * 24 * 60 * 60;
    uint64_t cutoff_time = current_time - retention_seconds;
    
    uint64_t pruned_bytes = 0;
    uint64_t pruned_blocks = 0;
    
    /* In real implementation:
     * 1. Find blocks older than cutoff
     * 2. Generate pruning proof
     * 3. Delete transaction data (keep headers)
     * 4. Update storage metrics
     */
    
    printf("Node pruning: Removed %lu blocks (%lu MB)\n",
           pruned_blocks, pruned_bytes / (1024 * 1024));
    
    return pruned_bytes;
}

/* Get storage used by node */
uint64_t cmptr_blockchain_get_storage_used(const node_t* node) {
    if (!node || !node->blockchain) return 0;
    
    return calculate_storage_required(node, node->blockchain->height);
}

/* Storage tier info */
void print_storage_tier_info(const storage_config_t* config, const char* name) {
    printf("\n%s Storage Tier:\n", name);
    printf("  Retention: ");
    if (config->retention_days == 0) {
        printf("Forever\n");
    } else {
        printf("%lu days\n", config->retention_days);
    }
    printf("  Store transactions: %s\n", config->store_transactions ? "Yes" : "No");
    printf("  Store proofs: %s\n", config->store_proofs ? "Yes" : "No");
    printf("  Store witnesses: %s\n", config->store_witnesses ? "Yes" : "No");
    printf("  Max storage: ");
    if (config->max_storage_gb == 0) {
        printf("Unlimited\n");
    } else {
        printf("%lu GB\n", config->max_storage_gb);
    }
}

/* Estimate storage for different tiers */
void estimate_storage_requirements(uint64_t years) {
    uint64_t blocks_per_year = (365 * 24 * 60 * 60) / 10;  /* 10 second blocks */
    uint64_t total_blocks = blocks_per_year * years;
    
    printf("\nStorage estimates after %lu years (%lu blocks):\n", years, total_blocks);
    
    /* Archive node */
    uint64_t archive_storage = total_blocks * (1024 + 100000 * 256 + 3 * 190 * 1024);
    printf("  Archive node: %.2f TB\n", archive_storage / (1024.0 * 1024.0 * 1024.0 * 1024.0));
    
    /* Full node (1 year) */
    uint64_t full_blocks = blocks_per_year;
    uint64_t full_storage = total_blocks * 1024 + full_blocks * (100000 * 256 + 3 * 190 * 1024);
    printf("  Full node: %.2f GB\n", full_storage / (1024.0 * 1024.0 * 1024.0));
    
    /* Light node (30 days) */
    uint64_t light_blocks = blocks_per_year / 12;
    uint64_t light_storage = total_blocks * 1024 + light_blocks * 100000 * 256;
    printf("  Light node: %.2f GB\n", light_storage / (1024.0 * 1024.0 * 1024.0));
    
    /* Ultra-light (headers only) */
    uint64_t ultralight_storage = total_blocks * 1024;
    printf("  Ultra-light: %.2f GB\n", ultralight_storage / (1024.0 * 1024.0 * 1024.0));
    
    printf("\nNote: With PARKED/ACTIVE pruning, nullifier storage stays constant at ~3.2GB\n");
}