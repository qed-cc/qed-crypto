/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
#include "sha3.h"
#include <string.h>
#ifdef __GNUC__
#include <immintrin.h>
static inline int _sha3_cpu_has_avx2(void) { return __builtin_cpu_supports("avx2"); }
static inline int _sha3_cpu_has_avx512f(void) { return __builtin_cpu_supports("avx512f"); }
extern int sha3_hash_256_64B_avx2(const void *data, size_t len, void *digest, size_t digest_size);
extern int sha3_hash_256_64B_avx512(const void *data, size_t len, void *digest, size_t digest_size);
#endif

/*
 * SHA3 core implementation (one-shot and incremental API)
 *
 * This file implements the public API functions declared in sha3.h:
 *  - sha3_init, sha3_update, sha3_final for incremental hashing
 *  - sha3_hash for one-shot hashing with optional runtime dispatch to
 *    optimized AVX2/AVX-512 kernels on x86-64 (64-byte inputs)
 *  - shake_xof for variable-length output functions (SHAKE128/SHAKE256)
 *  - Helper functions: sha3_get_digest_size, sha3_get_block_size, sha3_version
 *
 * Internally, Keccak-f[1600] permutation and sponge operations are provided
 * by keccak_init, keccak_absorb, keccak_permutation, and keccak_squeeze.
 */

/* Forward declarations of internal functions */
extern int keccak_init(uint64_t state[25]);
extern void keccak_absorb(uint64_t *state, const uint8_t *data, size_t len, size_t rate);
extern void keccak_permutation(uint64_t *state);
extern void keccak_squeeze(uint64_t *state, uint8_t *output, size_t output_len, size_t rate);

static const char *VERSION = "SHA3 Library 1.0.0";

/* Initialize SHA3 context */
int sha3_init(sha3_ctx *ctx, sha3_hash_type type) {
    if (!ctx) {
        return -1;
    }
    
    /* Clear state */
    memset(ctx, 0, sizeof(sha3_ctx));
    ctx->type = type;
    
    /* Set rate and domain suffix based on hash type */
    switch (type) {
        case SHA3_224:
            ctx->rate = SHA3_224_BLOCK_SIZE;
            ctx->domain_suffix = 0x06;
            break;
        case SHA3_256:
            ctx->rate = SHA3_256_BLOCK_SIZE;
            ctx->domain_suffix = 0x06;
            break;
        case SHA3_384:
            ctx->rate = SHA3_384_BLOCK_SIZE;
            ctx->domain_suffix = 0x06;
            break;
        case SHA3_512:
            ctx->rate = SHA3_512_BLOCK_SIZE;
            ctx->domain_suffix = 0x06;
            break;
        case SHAKE_128:
            ctx->rate = SHAKE_128_BLOCK_SIZE;
            ctx->domain_suffix = 0x1F;
            break;
        case SHAKE_256:
            ctx->rate = SHAKE_256_BLOCK_SIZE;
            ctx->domain_suffix = 0x1F;
            break;
        default:
            return -1;
    }
    
    /* Initialize Keccak state */
    return keccak_init(ctx->state);
}
// blank line to ensure newline at end-of-file

  

/* Update SHA3 context with new data */
int sha3_update(sha3_ctx *ctx, const void *data, size_t len) {
    const uint8_t *input = (const uint8_t *)data;
    size_t to_copy;
    
    if (!ctx || !input) {
        return -1;
    }
    
    /* Process data */
    while (len > 0) {
        /* Calculate how many bytes we can add to the buffer */
        to_copy = ctx->rate - ctx->buffer_pos;
        if (to_copy > len) {
            to_copy = len;
        }
        
        /* Copy data into the buffer */
        memcpy(ctx->buffer + ctx->buffer_pos, input, to_copy);
        ctx->buffer_pos += to_copy;
        input += to_copy;
        len -= to_copy;
        
        /* If the buffer is full, absorb it */
        if (ctx->buffer_pos == ctx->rate) {
            keccak_absorb(ctx->state, ctx->buffer, ctx->rate, ctx->rate);
            ctx->buffer_pos = 0;
        }
    }
    
    return 0;
}

/* Finalize SHA3 hash and get digest */
int sha3_final(sha3_ctx *ctx, void *digest, size_t digest_size) {
    uint8_t *output = (uint8_t *)digest;
    size_t hash_size;
    
    if (!ctx || !output) {
        return -1;
    }
    
    /* Get the hash size for this hash type */
    hash_size = sha3_get_digest_size(ctx->type);
    if (hash_size == 0 || digest_size < hash_size) {
        return -1;
    }
    
    /* Add the domain separation suffix */
    ctx->buffer[ctx->buffer_pos++] = ctx->domain_suffix;
    
    /* Add padding */
    memset(ctx->buffer + ctx->buffer_pos, 0, ctx->rate - ctx->buffer_pos);
    ctx->buffer[ctx->rate - 1] |= 0x80;
    
    /* Absorb the final block */
    keccak_absorb(ctx->state, ctx->buffer, ctx->rate, ctx->rate);
    
    /* Squeeze the output */
    keccak_squeeze(ctx->state, output, hash_size, ctx->rate);
    
    /* Clear sensitive data */
    memset(ctx->buffer, 0, sizeof(ctx->buffer));
    
    return hash_size;
}

/* Compute hash in one operation */
int sha3_hash(sha3_hash_type type, const void *data, size_t len, void *digest, size_t digest_size) {
    sha3_ctx ctx;
    int result;
    
    /* Specialized AVX2 path for 64-byte SHA3-256 */
    /* Specialized AVX2 and AVX-512 paths for 64-byte SHA3-256 */
    /* Specialized AVX-512 and AVX2 paths for 64-byte SHA3-256 */
    /* Initialize context */
    if (sha3_init(&ctx, type) != 0) {
        return -1;
    }
    
    /* Process data */
    if (sha3_update(&ctx, data, len) != 0) {
        return -1;
    }
    
    /* Finalize and get digest */
    result = sha3_final(&ctx, digest, digest_size);
    
    return result;
}

/* Get digest size for a hash type */
size_t sha3_get_digest_size(sha3_hash_type type) {
    switch (type) {
        case SHA3_224:
            return SHA3_224_DIGEST_SIZE;
        case SHA3_256:
            return SHA3_256_DIGEST_SIZE;
        case SHA3_384:
            return SHA3_384_DIGEST_SIZE;
        case SHA3_512:
            return SHA3_512_DIGEST_SIZE;
        case SHAKE_128:
        case SHAKE_256:
            return 0; /* Variable length for SHAKE */
        default:
            return 0;
    }
}

/* Get block size for a hash type */
size_t sha3_get_block_size(sha3_hash_type type) {
    switch (type) {
        case SHA3_224:
            return SHA3_224_BLOCK_SIZE;
        case SHA3_256:
            return SHA3_256_BLOCK_SIZE;
        case SHA3_384:
            return SHA3_384_BLOCK_SIZE;
        case SHA3_512:
            return SHA3_512_BLOCK_SIZE;
        case SHAKE_128:
            return SHAKE_128_BLOCK_SIZE;
        case SHAKE_256:
            return SHAKE_256_BLOCK_SIZE;
        default:
            return 0;
    }
}

/* Get library version string */
const char* sha3_version(void) {
    return VERSION;
}

/*
 * SHAKE XOF implementation (SHAKE128, SHAKE256)
 *
 * This function initializes the sponge with the appropriate domain suffix,
 * absorbs input data, applies multi-rate padding, and squeezes the
 * requested number of output bytes.
 */
int shake_xof(sha3_hash_type type, const void *data, size_t len, void *output, size_t output_len) {
    sha3_ctx ctx;
    
    /* Only SHAKE_128 and SHAKE_256 are supported */
    if (type != SHAKE_128 && type != SHAKE_256) {
        return -1;
    }
    
    /* Initialize context */
    if (sha3_init(&ctx, type) != 0) {
        return -1;
    }
    
    /* Process data */
    if (sha3_update(&ctx, data, len) != 0) {
        return -1;
    }
    
    /* Add the domain separation suffix */
    ctx.buffer[ctx.buffer_pos++] = ctx.domain_suffix;
    
    /* Add padding */
    memset(ctx.buffer + ctx.buffer_pos, 0, ctx.rate - ctx.buffer_pos);
    ctx.buffer[ctx.rate - 1] |= 0x80;
    
    /* Absorb the final block */
    keccak_absorb(ctx.state, ctx.buffer, ctx.rate, ctx.rate);
    
    /* Squeeze the output */
    keccak_squeeze(ctx.state, output, output_len, ctx.rate);
    
    /* Clear sensitive data */
    memset(ctx.buffer, 0, sizeof(ctx.buffer));
    
    return output_len;
}
