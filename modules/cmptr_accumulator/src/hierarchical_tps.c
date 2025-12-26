/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_accumulator.h"
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Calculate hierarchical TPS */
uint64_t calculate_hierarchical_tps(
    uint32_t num_aggregators,
    uint32_t num_generators,
    uint32_t num_producers
) {
    /* Each aggregator: 1000 TPS */
    uint64_t aggregator_tps = num_aggregators * 1000;
    
    /* Each generator can handle 10 aggregators */
    uint64_t generator_capacity = num_generators * 10 * 1000;
    
    /* Each producer can handle 10 generators */
    uint64_t producer_capacity = num_producers * 10 * 10 * 1000;
    
    /* Bottleneck determines actual TPS */
    uint64_t min_tps = aggregator_tps;
    if (generator_capacity < min_tps) min_tps = generator_capacity;
    if (producer_capacity < min_tps) min_tps = producer_capacity;
    
    return min_tps;
}