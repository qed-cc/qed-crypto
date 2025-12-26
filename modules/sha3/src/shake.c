/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
#include "sha3.h"
#include <string.h>

/* SHAKE-specific functions */

/* Initialize SHAKE128 context */
int shake128_init(void *context) {
    sha3_ctx *ctx = (sha3_ctx *)context;
    
    if (!ctx) {
        return -1;
    }
    
    return sha3_init(ctx, SHAKE_128);
}

/* Initialize SHAKE256 context */
int shake256_init(void *context) {
    sha3_ctx *ctx = (sha3_ctx *)context;
    
    if (!ctx) {
        return -1;
    }
    
    return sha3_init(ctx, SHAKE_256);
}

/* Specialized SHAKE squeeze functions (for internal use) */
static int shake_final_internal(sha3_ctx *ctx, void *output, size_t output_len) {
    uint8_t *out = (uint8_t *)output;
    size_t to_copy;
    
    /* Externally declared in keccak.c */
    extern void keccak_squeeze(uint64_t state[25], uint8_t *output, size_t output_len, size_t rate);
    extern void keccak_permutation(uint64_t state[25]);
    
    if (!ctx || !output) {
        return -1;
    }
    
    /* Add the domain separation suffix */
    ctx->buffer[ctx->buffer_pos++] = ctx->domain_suffix;
    
    /* Add padding */
    memset(ctx->buffer + ctx->buffer_pos, 0, ctx->rate - ctx->buffer_pos);
    ctx->buffer[ctx->rate - 1] |= 0x80;
    
    /* Absorb the final block */
    for (size_t i = 0; i < ctx->rate/8; i++) {
        ctx->state[i] ^= ((uint64_t*)ctx->buffer)[i];
    }
    
    /* Apply the permutation */
    keccak_permutation(ctx->state);
    
    /* Generate output */
    to_copy = ctx->rate;
    if (to_copy > output_len) {
        to_copy = output_len;
    }
    
    /* Copy first block of output */
    memcpy(out, ctx->state, to_copy);
    output_len -= to_copy;
    out += to_copy;
    
    /* Generate additional blocks if needed */
    while (output_len > 0) {
        keccak_permutation(ctx->state);
        
        to_copy = ctx->rate;
        if (to_copy > output_len) {
            to_copy = output_len;
        }
        
        memcpy(out, ctx->state, to_copy);
        output_len -= to_copy;
        out += to_copy;
    }
    
    /* Clear sensitive data */
    memset(ctx->buffer, 0, sizeof(ctx->buffer));
    
    return 0;
}

/* SHAKE128 final */
int shake128_final(void *context, void *digest, size_t digest_size) {
    sha3_ctx *ctx = (sha3_ctx *)context;
    
    if (!ctx || ctx->type != SHAKE_128) {
        return -1;
    }
    
    return shake_final_internal(ctx, digest, digest_size) == 0 ? (int)digest_size : -1;
}

/* SHAKE256 final */
int shake256_final(void *context, void *digest, size_t digest_size) {
    sha3_ctx *ctx = (sha3_ctx *)context;
    
    if (!ctx || ctx->type != SHAKE_256) {
        return -1;
    }
    
    return shake_final_internal(ctx, digest, digest_size) == 0 ? (int)digest_size : -1;
}