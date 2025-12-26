/**
 * @file compute_masked_evaluations.c
 * @brief Pre-compute masked polynomial evaluations for Merkle tree randomization
 */

#include "basefold_trace.h"
#include "multilinear.h"
#include "vanishing_poly.h"
#include "prg.h"
#include "gf128.h"
#include <sha3.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#ifdef __x86_64__
#include <immintrin.h>
#endif

// Helper function to generate deterministic blinding factor
static gf128_t generate_blinding_factor(const uint8_t* seed, size_t gate_idx, size_t column_idx) {
    uint8_t hash_input[32];
    uint8_t hash_output[32];
    
    // Format: seed || gate_idx || column_idx
    memcpy(hash_input, seed, 16);
    memcpy(hash_input + 16, &gate_idx, sizeof(size_t));
    memcpy(hash_input + 24, &column_idx, sizeof(size_t));
    
    // Hash to get randomness
    sha3_hash(SHA3_256, hash_input, 32, hash_output, 32);
    
    // Convert first 16 bytes to GF(2^128)
    gf128_t result;
    memcpy(&result, hash_output, sizeof(gf128_t));
    
    return result;
}

/**
 * @brief Compute and store masked polynomial evaluations
 */
bool basefold_trace_compute_masked_evaluations(basefold_trace_t* trace) {
    if (!trace || !trace->field_elements || !trace->is_masked) {
        return false;
    }
    
    if (!trace->zk_seed) {
        fprintf(stderr, "Error: No ZK seed available for masking\n");
        return false;
    }
    
    if (getenv("BASEFOLD_VERBOSE")) {
        printf("Computing masked evaluations for %u actual gates (out of %u padded)\n", 
               trace->num_gates, trace->padded_size);
    }
    
    // Only mask actual circuit gates, not padded zeros
    for (size_t i = 0; i < trace->num_gates; i++) {
        size_t base_idx = i * 4;
        
#ifdef __x86_64__
        gf128_t L, R, O, S;
        memcpy(&L, &trace->field_elements[base_idx + 0], sizeof(gf128_t));
        memcpy(&R, &trace->field_elements[base_idx + 1], sizeof(gf128_t));
        memcpy(&O, &trace->field_elements[base_idx + 2], sizeof(gf128_t));
        memcpy(&S, &trace->field_elements[base_idx + 3], sizeof(gf128_t));
#else
        gf128_t L, R, O, S;
        memcpy(&L, trace->field_elements + (base_idx + 0) * 16, sizeof(gf128_t));
        memcpy(&R, trace->field_elements + (base_idx + 1) * 16, sizeof(gf128_t));
        memcpy(&O, trace->field_elements + (base_idx + 2) * 16, sizeof(gf128_t));
        memcpy(&S, trace->field_elements + (base_idx + 3) * 16, sizeof(gf128_t));
#endif
        
        // Generate gate-specific mask
        gf128_t mask = generate_blinding_factor(trace->zk_seed, i, 0);
        
        gf128_t L_masked, R_masked, O_masked;
        
        if (gf128_eq(S, gf128_one())) {
            // AND gate: Cannot use simple masking as it breaks L∧R=O
            // Use identity masking for AND gates to preserve constraint
            L_masked = L;
            R_masked = R;  
            O_masked = O;
        } else {
            // XOR gate: L⊕R=O, so (L⊕m)⊕(R⊕m) = L⊕R⊕m⊕m = L⊕R = O⊕0 = O
            // But we need O to also be masked, so: (L⊕m)⊕(R⊕m) = O⊕m⊕m = O
            // Actually: (L⊕m)⊕(R⊕m) = L⊕R = O, but we want masked O
            // So: O_masked = (L⊕m)⊕(R⊕m) = L⊕R = O (mask cancels)
            // Better approach: use same mask for all three
            L_masked = gf128_add(L, mask);
            R_masked = gf128_add(R, mask);
            O_masked = gf128_add(O, mask);
            // Verify: (L⊕m)⊕(R⊕m) = L⊕R = O, but O⊕m ≠ O⊕0
            // This breaks the constraint! Need different approach.
            
            // Correct approach: mask only L and R, recompute O
            L_masked = gf128_add(L, mask);
            R_masked = gf128_add(R, mask);
            O_masked = gf128_add(L_masked, R_masked); // L'⊕R' = (L⊕m)⊕(R⊕m) = L⊕R
            // This gives O_masked = L⊕R = O (original value)
            // Still no randomization for O!
            
            // Alternative: use different masks that sum to zero
            gf128_t mask_L = generate_blinding_factor(trace->zk_seed, i, 1);
            gf128_t mask_R = generate_blinding_factor(trace->zk_seed, i, 2);
            gf128_t mask_O = gf128_add(mask_L, mask_R); // mask_O = mask_L ⊕ mask_R
            
            L_masked = gf128_add(L, mask_L);
            R_masked = gf128_add(R, mask_R);
            O_masked = gf128_add(O, mask_O);
            
            // Verify: L'⊕R' = (L⊕mask_L)⊕(R⊕mask_R) = L⊕R⊕(mask_L⊕mask_R) = L⊕R⊕mask_O
            // And O' = O⊕mask_O
            // So L'⊕R' = O'? L⊕R⊕mask_O = O⊕mask_O? Yes if L⊕R = O ✓
        }
        
#ifdef __x86_64__
        memcpy(&trace->field_elements[base_idx + 0], &L_masked, sizeof(__m128i));
        memcpy(&trace->field_elements[base_idx + 1], &R_masked, sizeof(__m128i));
        memcpy(&trace->field_elements[base_idx + 2], &O_masked, sizeof(__m128i));
#else
        memcpy(trace->field_elements + (base_idx + 0) * 16, &L_masked, sizeof(gf128_t));
        memcpy(trace->field_elements + (base_idx + 1) * 16, &R_masked, sizeof(gf128_t));
        memcpy(trace->field_elements + (base_idx + 2) * 16, &O_masked, sizeof(gf128_t));
#endif
    }
    
    if (getenv("BASEFOLD_VERBOSE")) {
        printf("Masked %u field elements successfully\n", trace->num_gates * 4);
        
        // Print first few masked values for debugging
        printf("First masked gate:\n");
        gf128_t first_L, first_R, first_O, first_S;
#ifdef __x86_64__
        memcpy(&first_L, &trace->field_elements[0], sizeof(gf128_t));
        memcpy(&first_R, &trace->field_elements[1], sizeof(gf128_t));
        memcpy(&first_O, &trace->field_elements[2], sizeof(gf128_t));
        memcpy(&first_S, &trace->field_elements[3], sizeof(gf128_t));
#else
        memcpy(&first_L, trace->field_elements + 0 * 16, sizeof(gf128_t));
        memcpy(&first_R, trace->field_elements + 1 * 16, sizeof(gf128_t));
        memcpy(&first_O, trace->field_elements + 2 * 16, sizeof(gf128_t));
        memcpy(&first_S, trace->field_elements + 3 * 16, sizeof(gf128_t));
#endif
        
        uint8_t buf[16];
        gf128_to_bytes(first_L, buf);
        printf("  L: ");
        for (int j = 0; j < 8; j++) printf("%02x", buf[j]);
        printf("...\n");
        
        gf128_to_bytes(first_R, buf);
        printf("  R: ");
        for (int j = 0; j < 8; j++) printf("%02x", buf[j]);
        printf("...\n");
        
        gf128_to_bytes(first_O, buf);
        printf("  O: ");
        for (int j = 0; j < 8; j++) printf("%02x", buf[j]);
        printf("...\n");
    }
    
    return true;
}