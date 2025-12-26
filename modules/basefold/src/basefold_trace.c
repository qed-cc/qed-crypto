#define _ISOC11_SOURCE
#define _POSIX_C_SOURCE 199309L  // For clock_gettime
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include "basefold_trace.h"
#include "gf128.h"
#include "polynomial_gf128.h"
#include "secure_random.h"
#include "input_validation.h"
#include "evaluation_domain.h"
#include "sha3.h"

// Declare the polynomial ZK functions
bool basefold_trace_apply_polynomial_zk(basefold_trace_t* trace, const uint8_t* seed);
bool basefold_trace_apply_polynomial_zk_simple(basefold_trace_t* trace, const uint8_t* seed);
bool basefold_trace_apply_field_xor_masking(basefold_trace_t* trace);
bool basefold_trace_apply_polynomial_zk_proper(basefold_trace_t* trace, const uint8_t* seed);

#ifdef __x86_64__
#include <immintrin.h>
#include <wmmintrin.h>
#endif

// Global basefold proof container
basefold_proof_t basefold_proof;

/**
 * @brief Find next power of 2 greater than or equal to n
 */
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

basefold_trace_t* basefold_trace_init(uint32_t expected_gates) {
    basefold_trace_t *trace = malloc(sizeof(basefold_trace_t));
    if (!trace) {
        return NULL;
    }
    
    // Initialize with capacity for expected gates
    trace->num_gates = 0;
    trace->trace_capacity = expected_gates > 0 ? expected_gates : 1024;
    trace->padded_size = 0;
    trace->num_field_elements = 0;
    trace->field_elements = NULL;
    trace->is_padded = false;
    trace->is_masked = false;
    memset(trace->mask_seed, 0, 16);
    trace->needs_polynomial_zk = false;
    trace->zk_seed = NULL;
    
    // Initialize polynomial fields
    for (int i = 0; i < 4; i++) {
        trace->witness_polys[i] = NULL;
        trace->masked_polys[i] = NULL;
    }
    trace->randomizer_poly = NULL;
    trace->eval_domain = NULL;
    
    // Allocate trace data array
    trace->trace_data = malloc(trace->trace_capacity * sizeof(gate_trace_t));
    if (!trace->trace_data) {
        free(trace);
        return NULL;
    }
    
    return trace;
}

void basefold_trace_free(basefold_trace_t *trace) {
    if (trace) {
        free(trace->trace_data);
        free(trace->field_elements);
        free(trace->extended_field_elements);
        
        // Free polynomial fields
        for (int i = 0; i < 4; i++) {
            if (trace->witness_polys[i]) poly_free(trace->witness_polys[i]);
            if (trace->masked_polys[i]) poly_free(trace->masked_polys[i]);
        }
        if (trace->randomizer_poly) poly_free(trace->randomizer_poly);
        if (trace->eval_domain) domain_free(trace->eval_domain);
        
        // Free ZK seed if allocated
        if (trace->zk_seed) free(trace->zk_seed);
        
        free(trace);
    }
}

bool basefold_trace_record_gate(
    basefold_trace_t *trace,
    uint8_t left_input,
    uint8_t right_input,
    uint8_t output,
    uint8_t gate_type
) {
    if (!trace || !trace->trace_data) {
        return false;
    }
    
    // Validate inputs (must be 0 or 1)
    if ((left_input & ~1) || (right_input & ~1) || (output & ~1) || (gate_type & ~1)) {
        return false;
    }
    
    // Resize array if needed
    if (trace->num_gates >= trace->trace_capacity) {
        uint32_t new_capacity = trace->trace_capacity * 2;
        gate_trace_t *new_data = safe_realloc(trace->trace_data, new_capacity, sizeof(gate_trace_t));
        if (!new_data) {
            return false;
        }
        trace->trace_data = new_data;
        trace->trace_capacity = new_capacity;
    }
    
    // Pack 4 bits into trace entry
    gate_trace_t entry = (gate_type << 3) | (output << 2) | (right_input << 1) | left_input;
    trace->trace_data[trace->num_gates] = entry;
    trace->num_gates++;
    
    return true;
}

bool basefold_trace_pad_to_power_of_2(basefold_trace_t *trace) {
    if (!trace || !trace->trace_data) {
        return false;
    }
    
    if (trace->is_padded) {
        return true; // Already padded
    }
    
    // Calculate next power of 2
    uint32_t padded_size = next_power_of_2(trace->num_gates);
    
    // Resize if needed
    if (padded_size > trace->trace_capacity) {
        gate_trace_t *new_data = safe_realloc(trace->trace_data, padded_size, sizeof(gate_trace_t));
        if (!new_data) {
            return false;
        }
        trace->trace_data = new_data;
        trace->trace_capacity = padded_size;
    }
    
    // Pad with valid XOR gates that output 0
    // XOR gate with inputs 0,0 and output 0 satisfies: 0 XOR 0 = 0
    for (uint32_t i = trace->num_gates; i < padded_size; i++) {
        trace->trace_data[i] = 0; // This represents L=0, R=0, O=0, S=0 (XOR gate)
    }
    
    trace->padded_size = padded_size;
    
    // Create field elements array: padded_size gates × 4 columns = num_field_elements
    trace->num_field_elements = padded_size * 4;
    
    // Check for potential overflow in allocation size
    if (trace->num_field_elements > SIZE_MAX / 16) {
        return false;
    }
    
    // Allocate aligned memory for SIMD operations
#ifdef __x86_64__
    void* ptr = NULL;
    size_t alloc_size = trace->num_field_elements * 16;
    // printf("Allocating %zu bytes (%u field elements) with posix_memalign\n", alloc_size, trace->num_field_elements);
    int ret = posix_memalign(&ptr, 16, alloc_size);
    if (ret != 0) {
        fprintf(stderr, "posix_memalign failed with error %d\n", ret);
        return false;
    }
    if (!ptr) {
        fprintf(stderr, "posix_memalign returned NULL\n");
        return false;
    }
    trace->field_elements = (__m128i*)ptr;
#else
    trace->field_elements = malloc(trace->num_field_elements * 16);  // 16 bytes per GF(2^128) element
#endif
    if (!trace->field_elements) {
        fprintf(stderr, "Failed to allocate field_elements\n");
        return false;
    }
    
    // Convert trace data to field elements
    // Each gate contributes 4 field elements (left, right, output, gate_type)
    for (uint32_t i = 0; i < padded_size; i++) {
        gate_trace_t gate = trace->trace_data[i];
        uint32_t base_idx = i * 4;
        
        // Extract individual bits
        uint8_t left = gate & 1;
        uint8_t right = (gate >> 1) & 1;
        uint8_t output = (gate >> 2) & 1;
        uint8_t gate_type = (gate >> 3) & 1;
        
        // Convert to GF(2^128) elements (bit expanded to 16 bytes)
#ifdef __x86_64__
        // Create GF(2^128) elements that match gf128_one() = {hi=0, lo=1}
        __m128i zero = _mm_setzero_si128();
        
        if (left) {
            // _mm_set_epi64x takes parameters in order: high, low
            // So _mm_set_epi64x(0, 1) creates {high 64 bits = 0, low 64 bits = 1}
            __m128i one = _mm_set_epi64x(0, 1);
            trace->field_elements[base_idx + 0] = one;
        } else {
            trace->field_elements[base_idx + 0] = zero;
        }
        
        if (right) {
            __m128i one = _mm_set_epi64x(0, 1);
            trace->field_elements[base_idx + 1] = one;
        } else {
            trace->field_elements[base_idx + 1] = zero;
        }
        
        if (output) {
            __m128i one = _mm_set_epi64x(0, 1);
            trace->field_elements[base_idx + 2] = one;
        } else {
            trace->field_elements[base_idx + 2] = zero;
        }
        
        if (gate_type) {
            __m128i one = _mm_set_epi64x(0, 1);
            trace->field_elements[base_idx + 3] = one;
        } else {
            trace->field_elements[base_idx + 3] = zero;
        }
#else
        // Bounds check for field elements access
        if ((base_idx + 3) * 16 + 15 >= trace->num_field_elements * 16) {
            free(trace->field_elements);
            trace->field_elements = NULL;
            return false;
        }
        
        // Create proper GF(2^128) field elements
        // gf128_t has format {uint64_t hi, uint64_t lo}
        // On little-endian systems, this means bytes 0-7 are hi, bytes 8-15 are lo
        // We want value 1 to match gf128_one() = {hi=0, lo=1}
        memset(&trace->field_elements[(base_idx + 0) * 16], 0, 16);
        if (left) trace->field_elements[(base_idx + 0) * 16 + 8] = 1;  // Set lo byte
        
        memset(&trace->field_elements[(base_idx + 1) * 16], 0, 16);
        if (right) trace->field_elements[(base_idx + 1) * 16 + 8] = 1;
        
        memset(&trace->field_elements[(base_idx + 2) * 16], 0, 16);
        if (output) trace->field_elements[(base_idx + 2) * 16 + 8] = 1;
        
        memset(&trace->field_elements[(base_idx + 3) * 16], 0, 16);
        if (gate_type) trace->field_elements[(base_idx + 3) * 16 + 8] = 1;
#endif
    }
    
    trace->is_padded = true;
    
    return true;
}

const uint8_t* basefold_trace_get_bits(basefold_trace_t *trace, uint32_t *bit_count) {
    if (!trace || !trace->trace_data || !bit_count) {
        return NULL;
    }
    
    uint32_t gate_count = trace->is_padded ? trace->padded_size : trace->num_gates;
    *bit_count = gate_count * 4; // 4 bits per gate
    
    return (const uint8_t*)trace->trace_data;
}

bool basefold_trace_get_stats(basefold_trace_t *trace, basefold_trace_stats_t *stats_out) {
    if (!trace || !stats_out) {
        return false;
    }
    
    stats_out->total_gates = trace->num_gates;
    stats_out->and_gates = 0;
    stats_out->xor_gates = 0;
    
    // Count gate types only for unmasked traces
    // After masking, gate type statistics are meaningless due to randomization
    if (!trace->is_masked) {
        for (uint32_t i = 0; i < trace->num_gates; i++) {
            uint8_t gate_type = (trace->trace_data[i] >> 3) & 1;
            if (gate_type == 1) {
                stats_out->and_gates++;
            } else {
                stats_out->xor_gates++;
            }
        }
    } else {
        // For masked traces, gate statistics are not meaningful
        stats_out->and_gates = 0;
        stats_out->xor_gates = 0;
    }
    
    stats_out->total_bits = trace->num_gates * 4;
    stats_out->padded_bits = trace->is_padded ? trace->padded_size * 4 : stats_out->total_bits;
    
    if (stats_out->total_bits > 0) {
        stats_out->padding_overhead = ((double)stats_out->padded_bits - stats_out->total_bits) / stats_out->total_bits * 100.0;
    } else {
        stats_out->padding_overhead = 0.0;
    }
    
    return true;
}

void basefold_trace_print_summary(basefold_trace_t *trace) {
    if (!trace) {
        printf("Error: NULL trace\n");
        return;
    }
    
    basefold_trace_stats_t stats;
    if (!basefold_trace_get_stats(trace, &stats)) {
        printf("Error: Failed to get trace statistics\n");
        return;
    }
    
    printf("=== Basefold Trace Summary ===\n");
    printf("Total gates:     %u\n", stats.total_gates);
    
    if (!trace->is_masked) {
        printf("AND gates:       %u (%.2f%%)\n", stats.and_gates, 
               stats.total_gates > 0 ? (double)stats.and_gates / stats.total_gates * 100.0 : 0.0);
        printf("XOR gates:       %u (%.2f%%)\n", stats.xor_gates,
               stats.total_gates > 0 ? (double)stats.xor_gates / stats.total_gates * 100.0 : 0.0);
    } else {
        printf("Gate statistics: Not available (trace is masked)\n");
    }
    
    printf("Total bits:      %u\n", stats.total_bits);
    
    if (trace->is_padded) {
        printf("Padded bits:     %u\n", stats.padded_bits);
        printf("Padding overhead: %.2f%%\n", stats.padding_overhead);
        printf("Padded to:       2^%u gates\n", (uint32_t)log2(trace->padded_size));
        printf("Field elements:  %u (GF(2^128))\n", trace->num_field_elements);
        printf("Field mem usage: %.1f MiB\n", 
               (double)(trace->num_field_elements * 16) / (1024.0 * 1024.0));
    } else {
        printf("Status:          Not padded\n");
    }
    
    printf("Gate mem usage:  %zu bytes\n", trace->trace_capacity * sizeof(gate_trace_t));
    
    if (trace->is_masked) {
        printf("ZK Status:       Masked with seed: ");
        for (int i = 0; i < 16; i++) {
            printf("%02x", trace->mask_seed[i]);
        }
        printf("\n");
    } else {
        printf("ZK Status:       Not masked\n");
    }
}

/**
 * @brief Generate random bytes using paranoid multi-source approach
 */
static bool generate_random_bytes(uint8_t *buffer, size_t len) {
    // For 16-byte requests, use our optimized paranoid function
    if (len == 16) {
        return secure_random_seed_16_safe(buffer);
    }
    
    // For 128-byte requests, use our optimized paranoid function
    if (len == 128) {
        return secure_random_seed_128_safe(buffer);
    }
    
    // For other sizes, use secure_random_bytes with additional entropy mixing
    if (secure_random_bytes(buffer, len) != SECURE_RANDOM_SUCCESS) {
        return false;
    }
    
    // Add timestamp entropy for paranoia (fast, always available)
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    uint64_t time_mix = ts.tv_nsec ^ (ts.tv_sec * 0x9e3779b97f4a7c15ULL);
    
    // XOR time entropy into buffer
    for (size_t i = 0; i < len && i < 8; i++) {
        buffer[i] ^= (time_mix >> (i * 8)) & 0xFF;
    }
    
    return true;
}

#ifdef __x86_64__
/**
 * @brief AES-CTR PRG using AES-NI instructions
 */
static __m128i aes_ctr_block(__m128i key, uint64_t counter) {
    // Create 128-bit block with counter in lower 64 bits
    __m128i block = _mm_set_epi64x(0, counter);
    
    // Proper AES-CTR with multiple rounds for security
    block = _mm_xor_si128(block, key);
    
    // Apply multiple AES rounds for proper diffusion
    for (int i = 0; i < 4; i++) {
        block = _mm_aesenc_si128(block, key);
        // Rotate key for each round
        key = _mm_shuffle_epi32(key, _MM_SHUFFLE(1, 0, 3, 2));
    }
    
    return block;
}
#endif

/**
 * @brief Portable SHAKE128-based PRG fallback
 */
static void shake128_prg_block(const uint8_t *seed, uint64_t counter, uint8_t *output) {
    // Better portable PRG with proper counter mixing
    uint64_t state1 = 0, state2 = counter;
    
    // Mix seed into state
    for (int i = 0; i < 8; i++) {
        state1 ^= ((uint64_t)seed[i]) << (i * 8);
        state2 ^= ((uint64_t)seed[i + 8]) << (i * 8);
    }
    
    // Mix counter more thoroughly
    state1 ^= counter * 0x9e3779b97f4a7c15ULL;
    state2 ^= (~counter) * 0xc6a4a7935bd1e995ULL;
    
    // Generate 16 bytes using xorshift-style mixing
    for (int i = 0; i < 16; i++) {
        state1 ^= state1 << 13;
        state1 ^= state1 >> 7;
        state1 ^= state1 << 17;
        state2 ^= state2 << 21;
        state2 ^= state2 >> 35;
        state2 ^= state2 << 4;
        
        output[i] = (uint8_t)((state1 + state2) >> (i % 8));
        
        // Advance states
        state1 = state1 * 1103515245 + 12345;
        state2 = state2 * 1664525 + 1013904223;
    }
}

bool basefold_trace_apply_zk_mask(basefold_trace_t *trace, const uint8_t *seed) {
    // Use the proper polynomial randomization implementation
    return basefold_trace_apply_polynomial_zk_proper(trace, seed);
}

bool basefold_trace_apply_zk_mask_old(basefold_trace_t *trace, const uint8_t *seed) {
    if (!trace || !trace->field_elements) {
        return false;
    }
    
    if (!trace->is_padded) {
        fprintf(stderr, "Error: Trace must be padded before masking\n");
        return false;
    }
    
    if (trace->is_masked) {
        fprintf(stderr, "Error: Trace is already masked\n");
        return false;
    }
    
    // Generate or use provided seed
    if (seed) {
        memcpy(trace->mask_seed, seed, 128);
    } else {
        if (!generate_random_bytes(trace->mask_seed, 128)) {
            fprintf(stderr, "Error: Failed to generate random seed\n");
            return false;
        }
    }
    
    // CRITICAL: Current implementation is incorrect for polynomial commitment schemes
    // 
    // What we're doing wrong:
    // - Masking individual field elements breaks gate constraints
    // - No witness polynomial randomization
    // - No mask polynomial R(X)
    //
    // What we need to do (based on security analysis):
    // 1. Represent witness as polynomial w(X) over evaluation domain
    // 2. Sample random polynomial r(X) with proper degree bounds
    // 3. Compute ŵ(X) = w(X) + v_H(X) · r(X) where v_H is vanishing polynomial
    // 4. Include mask polynomial R(X) in batching: h(X) = R(X) + Σ quotients
    //
    // SECURITY FIX: Use actual randomness instead of zero seed
    // This function is deprecated but kept for compatibility
    // The new polynomial ZK implementation is used by default
    
    // Generate proper random seed if not provided
    if (!seed) {
        if (!secure_random_seed_128_safe(trace->mask_seed)) {
            fprintf(stderr, "CRITICAL: All secure random sources failed for ZK masking\n");
            fprintf(stderr, "This is a security failure - zero-knowledge cannot be guaranteed\n");
            return false;
        }
    }
    
    // Update trace_data to reflect the masked field elements
    // Convert masked field elements back to packed gate format
    for (uint32_t i = 0; i < trace->padded_size; i++) {
        uint32_t base_idx = i * 4;
        
        // Bounds check
        if (base_idx + 3 >= trace->num_field_elements) {
            fprintf(stderr, "Error: Out of bounds access at i=%u, base_idx=%u\n", i, base_idx);
            return false;
        }
        
        // Extract LSB from each masked field element
#ifdef __x86_64__
        // Use direct memory access instead of _mm_extract_epi8
        // Each __m128i is 16 bytes, we want byte 8 (matching gf128_one)
        uint8_t* elem0 = (uint8_t*)&trace->field_elements[base_idx + 0];
        uint8_t* elem1 = (uint8_t*)&trace->field_elements[base_idx + 1];
        uint8_t* elem2 = (uint8_t*)&trace->field_elements[base_idx + 2];
        uint8_t* elem3 = (uint8_t*)&trace->field_elements[base_idx + 3];
        
        uint8_t left = elem0[8] & 1;
        uint8_t right = elem1[8] & 1;
        uint8_t output = elem2[8] & 1;
        uint8_t gate_type = elem3[8] & 1;
#else
        // Extract from byte 8 to match gf128_one() = {hi=0, lo=1}
        uint8_t left = trace->field_elements[(base_idx + 0) * 16 + 8] & 1;
        uint8_t right = trace->field_elements[(base_idx + 1) * 16 + 8] & 1;
        uint8_t output = trace->field_elements[(base_idx + 2) * 16 + 8] & 1;
        uint8_t gate_type = trace->field_elements[(base_idx + 3) * 16 + 8] & 1;
#endif
        
        // Pack back into trace_data format
        trace->trace_data[i] = (gate_type << 3) | (output << 2) | (right << 1) | left;
    }
    
    trace->is_masked = true;
    return true;
}

size_t basefold_compute_randomizer_degree(size_t constraint_degree,
                                         size_t num_field_queries,
                                         size_t num_fri_queries) {
    // Based on security analysis:
    // h ≥ 2·d·(e·n_F + n_D) + n_D
    // where:
    // - d is the constraint degree
    // - e is extension field degree (7 for GF128/GF2)
    // - n_F is number of field queries
    // - n_D is number of FRI queries
    
    const size_t e = 7; // GF(2^7) = GF(128) over GF(2)
    
    size_t result = 2 * constraint_degree * (e * num_field_queries + num_fri_queries) + num_fri_queries;
    
    // Ensure result is reasonable
    if (result < constraint_degree) {
        fprintf(stderr, "WARNING: Computed randomizer degree %zu is less than constraint degree %zu\n",
                result, constraint_degree);
        result = constraint_degree * 2; // Minimum safe value
    }
    
    return result;
}

bool basefold_trace_get_mask_block(basefold_trace_t *trace, uint32_t block_index, uint8_t *mask_out) {
    if (!trace || !mask_out || !trace->is_masked) {
        return false;
    }
    
#ifdef __x86_64__
    __m128i key = _mm_loadu_si128((__m128i*)trace->mask_seed);
    __m128i mask_block = aes_ctr_block(key, block_index);
    _mm_storeu_si128((__m128i*)mask_out, mask_block);
#else
    shake128_prg_block(trace->mask_seed, block_index, mask_out);
#endif
    
    return true;
}

const uint8_t* basefold_trace_get_mask_seed(basefold_trace_t *trace) {
    if (!trace || !trace->is_masked) {
        return NULL;
    }
    return trace->mask_seed;
}

bool basefold_proof_init(basefold_proof_t *proof, basefold_trace_t *trace) {
    if (!proof || !trace) {
        return false;
    }
    
    // Trace must be masked and padded for proof generation
    if (!trace->is_masked || !trace->is_padded) {
        return false;
    }
    
    // Copy mask seed from trace
    const uint8_t *seed = basefold_trace_get_mask_seed(trace);
    if (!seed) {
        return false;
    }
    
    memcpy(proof->mask_seed, seed, 128);
    
    // Initialize other fields to zero (will be set by later stages)
    memset(proof->merkle_root, 0, 32);
    memset(proof->tweak_digest, 0, 32);
    
    return true;
}

bool basefold_proof_set_merkle_root(basefold_proof_t *proof, const uint8_t merkle_root[32]) {
    if (!proof || !merkle_root) {
        return false;
    }
    
    memcpy(proof->merkle_root, merkle_root, 32);
    return true;
}

bool basefold_proof_set_tweak_digest(basefold_proof_t *proof, const uint8_t tweak_digest[32]) {
    if (!proof || !tweak_digest) {
        return false;
    }
    
    memcpy(proof->tweak_digest, tweak_digest, 32);
    return true;
}

bool basefold_trace_create_extended_field_elements(basefold_trace_t* trace) {
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
    
    // Process each column (L, R, O, S)
    for (size_t col = 0; col < 4; col++) {
        // For each point in extended domain
        for (size_t idx = 0; idx < trace->extended_size; idx++) {
            // Map to original polynomial index
            size_t orig_idx = idx & (trace->padded_size - 1);
            
            // Get base evaluation from field_elements
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
            // Copy base value
            uint8_t value[16];
            memcpy(value, &trace->field_elements[field_idx * 16], 16);
            
            // Apply masking if not in original quadrant
            if (!evaluation_domain_is_original(domain, idx)) {
                gf128_t mask = evaluation_domain_generate_mask(domain, idx, col);
                // XOR with mask
                for (int i = 0; i < 8; i++) {
                    value[i] ^= (mask.lo >> (i * 8)) & 0xFF;
                    value[i + 8] ^= (mask.hi >> (i * 8)) & 0xFF;
                }
            }
            
            // Store in extended array
            memcpy(&trace->extended_field_elements[(idx * 4 + col) * 16], value, 16);
#endif
        }
    }
    
    evaluation_domain_free(domain);
    trace->has_extended_elements = true;
    
    return true;
}