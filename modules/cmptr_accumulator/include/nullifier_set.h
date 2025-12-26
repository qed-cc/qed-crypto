/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef NULLIFIER_SET_H
#define NULLIFIER_SET_H

#include <stdint.h>
#include <stdbool.h>

/* Nullifier set internal functions */
void update_bloom_filter(uint8_t bloom_filter[], size_t bloom_size, const uint8_t nullifier[32]);
bool check_bloom_filter(const uint8_t bloom_filter[], size_t bloom_size, const uint8_t nullifier[32]);

#endif /* NULLIFIER_SET_H */