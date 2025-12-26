/**
 * @file basefold_trace_parallel.c
 * @brief Parallel implementation of extended field element creation
 * 
 * Uses OpenMP to parallelize the mask generation across multiple cores
 */

#include "basefold_trace.h"
#include "evaluation_domain.h"
#include "extended_domain_utils.h"
#include <string.h>
#include <stdlib.h>
#ifdef _OPENMP
#include <omp.h>
#endif

bool basefold_trace_create_extended_field_elements_parallel(basefold_trace_t* trace) {
    if (!trace || !trace->field_elements || !trace->zk_seed || !trace->is_padded) {
        return false;
    }
    
    // Calculate dimensions
    size_t num_vars = 0;
    size_t temp = trace->padded_size;
    while (temp > 1) {
        num_vars++;
        temp >>= 1;
    }
    
    // Create evaluation domain
    evaluation_domain_t* domain = evaluation_domain_create(num_vars, trace->zk_seed);
    if (!domain) {
        return false;
    }
    
    // Set extended size
    trace->extended_size = domain->extended_size;
    trace->num_extended_elements = trace->extended_size * 4; // 4 columns: L, R, O, S
    
    // Allocate extended field elements
#ifdef __x86_64__
    void* ptr = NULL;
    size_t alloc_size = trace->num_extended_elements * 16;
    int ret = posix_memalign(&ptr, 16, alloc_size);
    if (ret != 0 || !ptr) {
        evaluation_domain_free(domain);
        return false;
    }
    trace->extended_field_elements = (__m128i*)ptr;
#else
    trace->extended_field_elements = malloc(trace->num_extended_elements * 16);
    if (!trace->extended_field_elements) {
        evaluation_domain_free(domain);
        return false;
    }
#endif
    
#ifdef _OPENMP
    // Parallel version - use all available cores
    #pragma omp parallel for schedule(dynamic, 1024)
    for (size_t idx = 0; idx < trace->extended_size; idx++) {
        // Map to original polynomial index
        size_t orig_idx = idx & (trace->padded_size - 1);
        
        // Process all 4 columns for this index
        for (size_t col = 0; col < 4; col++) {
            size_t field_idx = orig_idx * 4 + col;
            
#ifdef __x86_64__
            __m128i value = trace->field_elements[field_idx];
            
            // Apply masking if not in original quadrant
            if (!evaluation_domain_is_original(domain, idx)) {
                gf128_t mask = evaluation_domain_generate_mask(domain, idx, col);
                __m128i mask_vec = _mm_set_epi64x(mask.hi, mask.lo);
                value = _mm_xor_si128(value, mask_vec);
            }
            
            // Store in extended array
            trace->extended_field_elements[idx * 4 + col] = value;
#else
            // Non-x86_64 version
            uint8_t value[16];
            memcpy(value, &trace->field_elements[field_idx * 16], 16);
            
            if (!evaluation_domain_is_original(domain, idx)) {
                gf128_t mask = evaluation_domain_generate_mask(domain, idx, col);
                for (int i = 0; i < 8; i++) {
                    value[i] ^= ((uint8_t*)&mask.lo)[i];
                    value[i+8] ^= ((uint8_t*)&mask.hi)[i];
                }
            }
            
            memcpy(&trace->extended_field_elements[idx * 4 + col], value, 16);
#endif
        }
    }
#else
    // Sequential fallback - same as original
    for (size_t col = 0; col < 4; col++) {
        for (size_t idx = 0; idx < trace->extended_size; idx++) {
            size_t orig_idx = idx & (trace->padded_size - 1);
            size_t field_idx = orig_idx * 4 + col;
            
#ifdef __x86_64__
            __m128i value = trace->field_elements[field_idx];
            
            if (!evaluation_domain_is_original(domain, idx)) {
                gf128_t mask = evaluation_domain_generate_mask(domain, idx, col);
                __m128i mask_vec = _mm_set_epi64x(mask.hi, mask.lo);
                value = _mm_xor_si128(value, mask_vec);
            }
            
            trace->extended_field_elements[idx * 4 + col] = value;
#else
            uint8_t value[16];
            memcpy(value, &trace->field_elements[field_idx * 16], 16);
            
            if (!evaluation_domain_is_original(domain, idx)) {
                gf128_t mask = evaluation_domain_generate_mask(domain, idx, col);
                for (int i = 0; i < 8; i++) {
                    value[i] ^= ((uint8_t*)&mask.lo)[i];
                    value[i+8] ^= ((uint8_t*)&mask.hi)[i];
                }
            }
            
            memcpy(&trace->extended_field_elements[idx * 4 + col], value, 16);
#endif
        }
    }
#endif
    
    trace->has_extended_elements = true;
    evaluation_domain_free(domain);
    return true;
}