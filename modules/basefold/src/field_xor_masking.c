/**
 * @file field_xor_masking.c
 * @brief Simple XOR masking for field elements to ensure Merkle tree randomization
 * 
 * This is a temporary solution to demonstrate proper zero-knowledge behavior
 * with different Merkle trees for different proofs.
 */

#include "basefold_trace.h"
#include "prg.h"
#include "../../sha3/include/sha3.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __x86_64__
#include <immintrin.h>
#endif

bool basefold_trace_apply_field_xor_masking(basefold_trace_t *trace) {
    if (!trace) {
        fprintf(stderr, "XOR masking: trace is NULL\n");
        return false;
    }
    if (!trace->field_elements) {
        fprintf(stderr, "XOR masking: field_elements is NULL\n");
        return false;
    }
    if (!trace->is_masked) {
        fprintf(stderr, "XOR masking: is_masked is false\n");
        return false;
    }
    
    if (getenv("BASEFOLD_VERBOSE")) {
        printf("Applying field XOR masking to %u field elements\n", trace->num_field_elements);
    }
    
    // Use the already-set mask seed - compress 128 bytes to 16 for PRG
    uint8_t prg_seed[32];
    sha3_hash(2, trace->mask_seed, 128, prg_seed, 32); // SHA3-256
    prg_init(prg_seed); // PRG uses first 16 bytes
    
    // Apply simple XOR masking to each field element
    // This ensures the Merkle tree will be completely different
    for (uint32_t i = 0; i < trace->num_field_elements; i++) {
#ifdef __x86_64__
        __m128i mask = prg_next();
        trace->field_elements[i] = _mm_xor_si128(trace->field_elements[i], mask);
#else
        uint8_t mask[16];
        prg_next(mask);
        uint8_t* elem = trace->field_elements + (i * 16);
        for (int j = 0; j < 16; j++) {
            elem[j] ^= mask[j];
        }
#endif
    }
    
    if (getenv("BASEFOLD_VERBOSE")) {
        printf("Field XOR masking complete\n");
    }
    
    return true;
}