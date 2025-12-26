/**
 * @file wiring.c
 * @brief Wiring permutation implementation for BaseFold proofs
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include "input_validation.h"
#include "wiring.h"

static uint32_t next_power_of_2(uint32_t n) {
    if (n == 0) return 1;
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    return n + 1;
}

wiring_permutation_t* wiring_init(uint32_t expected_gates) {
    wiring_permutation_t *wiring = malloc(sizeof(wiring_permutation_t));
    if (!wiring) return NULL;
    
    // Allocate permutation array with some extra capacity
    uint32_t capacity = expected_gates > 0 ? expected_gates * 2 : 1024;
    wiring->sigma = malloc(capacity * sizeof(uint32_t));
    if (!wiring->sigma) {
        free(wiring);
        return NULL;
    }
    
    // Initialize all mappings to identity (self-mapping)
    for (uint32_t i = 0; i < capacity; i++) {
        wiring->sigma[i] = i;
    }
    
    wiring->num_gates = 0;
    wiring->padded_size = capacity;
    wiring->d = 0;
    wiring->is_padded = false;
    
    return wiring;
}

void wiring_free(wiring_permutation_t *wiring) {
    if (wiring) {
        free(wiring->sigma);
        free(wiring);
    }
}

bool wiring_add_gate(wiring_permutation_t *wiring, uint32_t gate_idx, 
                     uint32_t output_destination) {
    if (!wiring || !wiring->sigma) return false;
    
    // Resize if necessary
    if (gate_idx >= wiring->padded_size) {
        // SECURITY FIX: Check for overflow before adding 1
        if (gate_idx == UINT32_MAX) {
            fprintf(stderr, "Error: Gate index too large (%u)\n", gate_idx);
            fprintf(stderr, "Cannot resize wiring permutation beyond UINT32_MAX\n");
            return false;
        }
        uint32_t new_size = next_power_of_2(gate_idx + 1);
        uint32_t *new_sigma = safe_realloc(wiring->sigma, new_size, sizeof(uint32_t));
        if (!new_sigma) return false;
        
        // Initialize new entries to identity mapping
        for (uint32_t i = wiring->padded_size; i < new_size; i++) {
            new_sigma[i] = i;
        }
        
        wiring->sigma = new_sigma;
        wiring->padded_size = new_size;
    }
    
    // Set the wiring mapping
    wiring->sigma[gate_idx] = output_destination;
    
    // Update gate count
    if (gate_idx >= wiring->num_gates) {
        wiring->num_gates = gate_idx + 1;
    }
    
    return true;
}

bool wiring_pad_to_power_of_2(wiring_permutation_t *wiring) {
    if (!wiring || wiring->is_padded) return true;
    
    uint32_t target_size = next_power_of_2(wiring->num_gates);
    
    // Calculate d such that 2^d = target_size
    wiring->d = 0;
    uint32_t temp = target_size;
    while (temp > 1) {
        temp >>= 1;
        wiring->d++;
    }
    
    // CRITICAL FIX: Always resize to exact target_size, even if smaller than current padded_size
    uint32_t *new_sigma = safe_realloc(wiring->sigma, target_size, sizeof(uint32_t));
    if (!new_sigma) return false;
    
    // Initialize padding entries to identity mapping (only if growing)
    if (target_size > wiring->padded_size) {
        for (uint32_t i = wiring->padded_size; i < target_size; i++) {
            new_sigma[i] = i;
        }
    } else {
        // If shrinking, make sure remaining entries are valid
        for (uint32_t i = wiring->num_gates; i < target_size; i++) {
            new_sigma[i] = i;
        }
    }
    
    wiring->sigma = new_sigma;
    wiring->padded_size = target_size; // CRITICAL: Always update to exact target
    wiring->is_padded = true;
    return true;
}

uint32_t wiring_get_destination(const wiring_permutation_t *wiring, uint32_t gate_idx) {
    if (!wiring || !wiring->sigma || gate_idx >= wiring->padded_size) {
        return UINT32_MAX;
    }
    return wiring->sigma[gate_idx];
}

wiring_permutation_t* wiring_load_from_circuit(const char *circuit_file) {
    if (!circuit_file) return NULL;
    
    FILE *fp = fopen(circuit_file, "r");
    if (!fp) return NULL;
    
    // For now, implement a simple parser for basic circuit format
    // This would need to be adapted based on the actual circuit file format
    
    wiring_permutation_t *wiring = wiring_init(1000); // Start with reasonable capacity
    if (!wiring) {
        fclose(fp);
        return NULL;
    }
    
    char line[256];
    uint32_t gate_idx = 0;
    
    // Simple format: each line contains "gate_output_idx destination_idx"
    while (fgets(line, sizeof(line), fp)) {
        if (line[0] == '#' || line[0] == '\n') continue; // Skip comments and empty lines
        
        uint32_t output_idx, dest_idx;
        if (sscanf(line, "%u %u", &output_idx, &dest_idx) == 2) {
            if (!wiring_add_gate(wiring, output_idx, dest_idx)) {
                wiring_free(wiring);
                fclose(fp);
                return NULL;
            }
        }
    }
    
    fclose(fp);
    
    // Pad to power of 2
    if (!wiring_pad_to_power_of_2(wiring)) {
        wiring_free(wiring);
        return NULL;
    }
    
    return wiring;
}

wiring_permutation_t* wiring_generate_test(uint32_t num_gates, uint32_t seed) {
    if (num_gates == 0) return NULL;
    
    wiring_permutation_t *wiring = wiring_init(num_gates);
    if (!wiring) return NULL;
    
    // Use simple linear congruential generator for reproducible test data
    uint32_t state = seed;
    
    for (uint32_t i = 0; i < num_gates; i++) {
        // Generate pseudo-random destination within valid range
        state = state * 1103515245 + 12345;
        uint32_t dest = (state % num_gates);
        
        if (!wiring_add_gate(wiring, i, dest)) {
            wiring_free(wiring);
            return NULL;
        }
    }
    
    if (!wiring_pad_to_power_of_2(wiring)) {
        wiring_free(wiring);
        return NULL;
    }
    
    return wiring;
}

bool wiring_validate(const wiring_permutation_t *wiring) {
    if (!wiring || !wiring->sigma) return false;
    
    // Check that all destinations are within valid range
    for (uint32_t i = 0; i < wiring->padded_size; i++) {
        if (wiring->sigma[i] >= wiring->padded_size) {
            return false;
        }
    }
    
    // Check power-of-2 size if padded
    if (wiring->is_padded) {
        uint32_t expected_size = 1U << wiring->d;
        if (wiring->padded_size != expected_size) {
            return false;
        }
    }
    
    return true;
}

void wiring_print_summary(const wiring_permutation_t *wiring) {
    if (!wiring) {
        printf("Wiring: NULL\n");
        return;
    }
    
    printf("=== Wiring Permutation Summary ===\n");
    printf("Number of gates: %u\n", wiring->num_gates);
    printf("Padded size: %u\n", wiring->padded_size);
    printf("Depth parameter d: %u\n", wiring->d);
    printf("Is padded: %s\n", wiring->is_padded ? "yes" : "no");
    
    if (wiring->num_gates <= 16) {
        printf("Permutation mappings:\n");
        for (uint32_t i = 0; i < wiring->num_gates; i++) {
            printf("  gate[%u] -> row[%u]\n", i, wiring->sigma[i]);
        }
    } else {
        printf("First 8 mappings:\n");
        for (uint32_t i = 0; i < 8 && i < wiring->num_gates; i++) {
            printf("  gate[%u] -> row[%u]\n", i, wiring->sigma[i]);
        }
        printf("  ... (%u more)\n", wiring->num_gates - 8);
    }
    
    printf("Validation: %s\n", wiring_validate(wiring) ? "PASS" : "FAIL");
}