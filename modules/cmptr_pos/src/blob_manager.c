/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_pos.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Blob management for Narwhal DAG */

/* Create blob from transactions */
uint8_t* cmptr_pos_create_blob(
    transaction_t** transactions,
    uint32_t tx_count,
    uint32_t* blob_size_out
) {
    if (!transactions || tx_count == 0 || !blob_size_out) {
        return NULL;
    }
    
    /* Calculate blob size */
    size_t blob_size = sizeof(uint32_t); /* TX count */
    blob_size += tx_count * sizeof(transaction_t);
    
    uint8_t* blob = malloc(blob_size);
    if (!blob) {
        return NULL;
    }
    
    size_t offset = 0;
    
    /* Write transaction count */
    memcpy(blob + offset, &tx_count, sizeof(uint32_t));
    offset += sizeof(uint32_t);
    
    /* Write transactions */
    for (uint32_t i = 0; i < tx_count; i++) {
        memcpy(blob + offset, transactions[i], sizeof(transaction_t));
        offset += sizeof(transaction_t);
    }
    
    *blob_size_out = blob_size;
    
    printf("✓ Created blob: %u transactions, %zu bytes\n", tx_count, blob_size);
    
    return blob;
}

/* Parse blob to extract transactions */
transaction_t** cmptr_pos_parse_blob(
    const uint8_t* blob,
    uint32_t blob_size,
    uint32_t* tx_count_out
) {
    if (!blob || blob_size < sizeof(uint32_t) || !tx_count_out) {
        return NULL;
    }
    
    size_t offset = 0;
    
    /* Read transaction count */
    uint32_t tx_count;
    memcpy(&tx_count, blob + offset, sizeof(uint32_t));
    offset += sizeof(uint32_t);
    
    /* Validate size */
    size_t expected_size = sizeof(uint32_t) + (tx_count * sizeof(transaction_t));
    if (blob_size != expected_size) {
        fprintf(stderr, "Invalid blob size: %u != %zu\n", blob_size, expected_size);
        return NULL;
    }
    
    /* Allocate transaction array */
    transaction_t** transactions = calloc(tx_count, sizeof(transaction_t*));
    if (!transactions) {
        return NULL;
    }
    
    /* Read transactions */
    for (uint32_t i = 0; i < tx_count; i++) {
        transactions[i] = malloc(sizeof(transaction_t));
        memcpy(transactions[i], blob + offset, sizeof(transaction_t));
        offset += sizeof(transaction_t);
    }
    
    *tx_count_out = tx_count;
    
    return transactions;
}

/* Compress blob for network transmission */
uint8_t* cmptr_pos_compress_blob(
    const uint8_t* blob,
    uint32_t blob_size,
    uint32_t* compressed_size_out
) {
    if (!blob || blob_size == 0 || !compressed_size_out) {
        return NULL;
    }
    
    /* For demo: simple RLE compression */
    uint8_t* compressed = malloc(blob_size + 1024); /* Extra space for worst case */
    if (!compressed) {
        return NULL;
    }
    
    size_t out_pos = 0;
    
    /* Write original size */
    memcpy(compressed + out_pos, &blob_size, sizeof(uint32_t));
    out_pos += sizeof(uint32_t);
    
    /* Simple RLE encoding */
    for (uint32_t i = 0; i < blob_size; ) {
        uint8_t byte = blob[i];
        uint8_t count = 1;
        
        /* Count consecutive same bytes */
        while (i + count < blob_size && 
               blob[i + count] == byte && 
               count < 255) {
            count++;
        }
        
        /* Write count and byte */
        compressed[out_pos++] = count;
        compressed[out_pos++] = byte;
        
        i += count;
    }
    
    *compressed_size_out = out_pos;
    
    /* Resize to actual size */
    uint8_t* final = realloc(compressed, out_pos);
    
    printf("✓ Compressed blob: %u → %u bytes (%.1f%% ratio)\n",
           blob_size, (uint32_t)out_pos,
           (out_pos * 100.0) / blob_size);
    
    return final ? final : compressed;
}

/* Decompress blob */
uint8_t* cmptr_pos_decompress_blob(
    const uint8_t* compressed,
    uint32_t compressed_size,
    uint32_t* decompressed_size_out
) {
    if (!compressed || compressed_size < sizeof(uint32_t) || !decompressed_size_out) {
        return NULL;
    }
    
    size_t in_pos = 0;
    
    /* Read original size */
    uint32_t original_size;
    memcpy(&original_size, compressed + in_pos, sizeof(uint32_t));
    in_pos += sizeof(uint32_t);
    
    /* Allocate output */
    uint8_t* decompressed = malloc(original_size);
    if (!decompressed) {
        return NULL;
    }
    
    size_t out_pos = 0;
    
    /* RLE decoding */
    while (in_pos < compressed_size && out_pos < original_size) {
        uint8_t count = compressed[in_pos++];
        uint8_t byte = compressed[in_pos++];
        
        /* Write repeated bytes */
        for (uint8_t i = 0; i < count && out_pos < original_size; i++) {
            decompressed[out_pos++] = byte;
        }
    }
    
    if (out_pos != original_size) {
        free(decompressed);
        return NULL;
    }
    
    *decompressed_size_out = original_size;
    
    return decompressed;
}

/* Calculate blob hash */
void cmptr_pos_hash_blob(
    const uint8_t* blob,
    uint32_t blob_size,
    uint8_t* hash_out
) {
    if (!blob || blob_size == 0 || !hash_out) {
        return;
    }
    
    /* In real: use SHA3-256 */
    /* For demo: simple hash */
    memset(hash_out, 0, 32);
    
    uint32_t hash = 0x811C9DC5; /* FNV-1a init */
    
    for (uint32_t i = 0; i < blob_size; i++) {
        hash ^= blob[i];
        hash *= 0x01000193; /* FNV-1a prime */
    }
    
    memcpy(hash_out, &hash, 4);
    memcpy(hash_out + 4, &blob_size, 4);
    hash_out[0] ^= 0xBB; /* Blob marker */
}