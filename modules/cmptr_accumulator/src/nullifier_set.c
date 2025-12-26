/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_accumulator.h"
#include "nullifier_set.h"
#include <stdlib.h>
#include <string.h>

/* Update bloom filter with nullifier */
void update_bloom_filter(uint8_t bloom_filter[], size_t bloom_size, const uint8_t nullifier[32]) {
    /* Use 3 hash functions for bloom filter */
    uint32_t hash1 = *(uint32_t*)nullifier % (bloom_size * 8);
    uint32_t hash2 = *(uint32_t*)(nullifier + 4) % (bloom_size * 8);
    uint32_t hash3 = *(uint32_t*)(nullifier + 8) % (bloom_size * 8);
    
    bloom_filter[hash1 / 8] |= (1 << (hash1 % 8));
    bloom_filter[hash2 / 8] |= (1 << (hash2 % 8));
    bloom_filter[hash3 / 8] |= (1 << (hash3 % 8));
}

/* Check bloom filter */
bool check_bloom_filter(const uint8_t bloom_filter[], size_t bloom_size, const uint8_t nullifier[32]) {
    uint32_t hash1 = *(uint32_t*)nullifier % (bloom_size * 8);
    uint32_t hash2 = *(uint32_t*)(nullifier + 4) % (bloom_size * 8);
    uint32_t hash3 = *(uint32_t*)(nullifier + 8) % (bloom_size * 8);
    
    return (bloom_filter[hash1 / 8] & (1 << (hash1 % 8))) &&
           (bloom_filter[hash2 / 8] & (1 << (hash2 % 8))) &&
           (bloom_filter[hash3 / 8] & (1 << (hash3 % 8)));
}