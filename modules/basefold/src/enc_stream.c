#define _ISOC11_SOURCE
#include "enc.h"
#include "gf128.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Streaming encoder for memory-constrained environments
// Processes data in 1 MiB slabs to keep memory usage ≤ 32 MiB

#define SLAB_SIZE_WORDS (1 << 16)  // 64K words = 1 MiB per slab
#define SLAB_SIZE_BYTES (SLAB_SIZE_WORDS * 16)

void enc_fold_stream(size_t d, FILE *f_in, FILE *f_tmp)
{
    gf128_t *bufL = aligned_alloc(64, SLAB_SIZE_BYTES);
    gf128_t *bufR = aligned_alloc(64, SLAB_SIZE_BYTES);
    
    if (!bufL || !bufR) {
        free(bufL);
        free(bufR);
        return; // Memory allocation failed
    }
    
    for (size_t r = 0; r < d; ++r) {
        rewind(f_in);
        fseek(f_tmp, 0, SEEK_SET);
        
        size_t total_words = (size_t)1 << (d + 1 - r); // Words in this round
        gf128_t tweak = enc_get_tweak(r);
        
        size_t written = 0;
        
        while (written < total_words / 2) {
            size_t chunk_words = SLAB_SIZE_WORDS;
            if (written + chunk_words > total_words / 2) {
                chunk_words = total_words / 2 - written;
            }
            
            // Read left and right halves
            size_t readL = fread(bufL, 16, chunk_words, f_in);
            size_t readR = fread(bufR, 16, chunk_words, f_in);
            
            if (readL != chunk_words || readR != chunk_words) {
                break; // Read error or EOF
            }
            
            // Apply fold transformation in-place
            for (size_t i = 0; i < chunk_words; ++i) {
                gf128_t L = bufL[i];
                gf128_t R = bufR[i];
                
                gf128_t TR = gf128_mul(tweak, R);
                gf128_t sum = gf128_add(L, TR);         // L + T_r·R
                gf128_t diff = gf128_add(sum, R);       // L + T_r·R + R
                
                bufL[i] = sum;   // First half result
                bufR[i] = diff;  // Second half result
            }
            
            // Write results to temporary file
            fwrite(bufL, 16, chunk_words, f_tmp);
            fwrite(bufR, 16, chunk_words, f_tmp);
            
            written += chunk_words;
        }
        
        // Swap input and temporary files for next round
        FILE *swap = f_in;
        f_in = f_tmp;
        f_tmp = swap;
    }
    
    free(bufL);
    free(bufR);
}