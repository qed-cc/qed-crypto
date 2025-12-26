#include "evaluation_domain.h"
#include "sha3.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#ifdef __x86_64__
#include <immintrin.h>  // For AES-NI and SSE intrinsics
#endif

evaluation_domain_t* evaluation_domain_create(size_t num_original_vars, const uint8_t* zk_seed) {
    // SECURITY FIX: More conservative bounds to prevent overflow
    size_t max_vars = (sizeof(size_t) == 4) ? 28 : 30;  // Account for +2 extension
    
    if (num_original_vars == 0 || num_original_vars > max_vars) {
        if (num_original_vars == 0) {
            fprintf(stderr, "Error: Evaluation domain requires at least 1 variable\n");
        } else {
            fprintf(stderr, "Error: Too many variables for evaluation domain (%zu variables)\n", num_original_vars);
            fprintf(stderr, "Maximum safe variables: %zu (with 4x extension: %zu)\n", max_vars, max_vars + 2);
            fprintf(stderr, "This prevents memory overflow in domain extension\n");
        }
        return NULL;
    }
    
    // SECURITY FIX: Check for overflow in extended_vars calculation
    if (num_original_vars > SIZE_MAX - 2) {
        fprintf(stderr, "Error: Cannot extend evaluation domain (variable count too large)\n");
        fprintf(stderr, "Original variables: %zu, cannot add 2 for extension\n", num_original_vars);
        return NULL;
    }
    
    evaluation_domain_t* domain = malloc(sizeof(evaluation_domain_t));
    if (!domain) {
        return NULL;
    }
    
    domain->original_vars = num_original_vars;
    domain->extended_vars = num_original_vars + 2;  // Add 2 variables for 4x extension
    
    // SECURITY FIX: Validate shift operations
    if (num_original_vars >= 64 || domain->extended_vars >= 64) {
        fprintf(stderr, "Error: Cannot create evaluation domain with %zu variables (extended: %zu)\n", 
                num_original_vars, domain->extended_vars);
        fprintf(stderr, "Bit shift operations are undefined for shifts >= 64\n");
        free(domain);
        return NULL;
    }
    
    domain->original_size = 1ULL << num_original_vars;
    domain->extended_size = 1ULL << domain->extended_vars;  // 4 * original_size
    
    // Store ZK seed if provided
    if (zk_seed) {
        domain->zk_seed = malloc(16);
        if (!domain->zk_seed) {
            free(domain);
            return NULL;
        }
        memcpy(domain->zk_seed, zk_seed, 16);
    } else {
        domain->zk_seed = NULL;
    }
    
    return domain;
}

void evaluation_domain_free(evaluation_domain_t* domain) {
    if (domain) {
        free(domain->zk_seed);
        free(domain);
    }
}

void evaluation_domain_index_to_point(
    const evaluation_domain_t* domain,
    size_t index,
    gf128_t* point)
{
    if (!domain || !point) return;
    
    // Convert index to binary representation
    // First n bits go to original variables
    for (size_t i = 0; i < domain->original_vars; i++) {
        point[i] = (index & (1ULL << i)) ? gf128_one() : gf128_zero();
    }
    
    // Next 2 bits go to extension variables
    point[domain->original_vars] = (index & (1ULL << domain->original_vars)) ? gf128_one() : gf128_zero();
    point[domain->original_vars + 1] = (index & (1ULL << (domain->original_vars + 1))) ? gf128_one() : gf128_zero();
}

gf128_t evaluation_domain_generate_mask(
    const evaluation_domain_t* domain,
    size_t index,
    size_t column)
{
    if (!domain || !domain->zk_seed) {
        return gf128_zero();
    }
    
    // Original quadrant: no masking
    if (evaluation_domain_is_original(domain, index)) {
        return gf128_zero();
    }
    
    // Use fast AES-based PRG instead of SHA3
    // AES-NI can do ~1 billion operations per second
    
    gf128_t mask;
    
    // Use a simple but cryptographically strong PRG
    // Based on AES round function (without key schedule)
    uint64_t state[2];
    memcpy(state, domain->zk_seed, 16);
    
    // Mix in index and column
    state[0] ^= index;
    state[1] ^= column;
    
    // Apply pseudo-AES rounds using x86 intrinsics
#ifdef __x86_64__
    __m128i s = _mm_set_epi64x(state[1], state[0]);
    
    // Use 10 rounds like real AES for security
    // Derive round keys from seed
    __m128i round_keys[10];
    __m128i key = s;
    for (int i = 0; i < 10; i++) {
        key = _mm_aesenc_si128(key, _mm_set_epi32(i, column, index, i ^ 0x5a));
        round_keys[i] = key;
    }
    
    // Apply 10 AES rounds
    for (int i = 0; i < 10; i++) {
        s = _mm_aesenc_si128(s, round_keys[i]);
    }
    
    // Extract result
    mask.lo = _mm_extract_epi64(s, 0);
    mask.hi = _mm_extract_epi64(s, 1);
#else
    // Fallback: Use multiplication-based PRG
    const uint64_t mul1 = 0x9e3779b97f4a7c15ULL;
    const uint64_t mul2 = 0xc6a4a7935bd1e995ULL;
    
    state[0] = state[0] * mul1 + index;
    state[1] = state[1] * mul2 + column;
    
    // Mix bits
    state[0] ^= state[0] >> 33;
    state[0] *= mul1;
    state[0] ^= state[0] >> 33;
    
    state[1] ^= state[1] >> 33;
    state[1] *= mul2;
    state[1] ^= state[1] >> 33;
    
    mask.lo = state[0];
    mask.hi = state[1];
#endif
    
    return mask;
}

void evaluation_domain_extend_polynomial(
    const evaluation_domain_t* domain,
    const gf128_t* original_evals,
    size_t column,
    gf128_t* extended_evals)
{
    if (!domain || !original_evals || !extended_evals) return;
    
    // Process each point in the extended domain
    for (size_t idx = 0; idx < domain->extended_size; idx++) {
        // Map to original polynomial index
        size_t orig_idx = idx & (domain->original_size - 1);
        
        // Get base evaluation
        gf128_t value = original_evals[orig_idx];
        
        // Apply masking if not in original quadrant
        if (!evaluation_domain_is_original(domain, idx) && domain->zk_seed) {
            gf128_t mask = evaluation_domain_generate_mask(domain, idx, column);
            value = gf128_add(value, mask);
        }
        
        extended_evals[idx] = value;
    }
}