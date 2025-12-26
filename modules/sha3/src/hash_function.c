/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
/**
 * @file hash_function.c
 * @brief Pluggable hash function interface implementation for SHA3 and SHAKE.
 *
 * This file provides wrappers that conform to the sha3_hash_function interface,
 * allowing SHA3 and SHAKE (XOF) functions to be used in generic hashing frameworks.
 * It defines static instances for each supported algorithm and helper routines
 * to create and free customizable hash function objects.
 */
#include "sha3.h"
#include <stdlib.h>
#include <string.h>

/* Forward declarations for wrapper functions */
static int sha3_224_init_wrapper(void *ctx);
static int sha3_256_init_wrapper(void *ctx);
static int sha3_384_init_wrapper(void *ctx);
static int sha3_512_init_wrapper(void *ctx);
static int sha3_update_wrapper(void *ctx, const void *data, size_t len);
static int sha3_final_wrapper(void *ctx, void *digest, size_t digest_size);

/* Static instances of hash functions */
static sha3_hash_function sha3_224_hash_function = {
    .init = sha3_224_init_wrapper,
    .update = sha3_update_wrapper,
    .final = sha3_final_wrapper,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = SHA3_224_DIGEST_SIZE,
    .name = "SHA3-224"
};

static sha3_hash_function sha3_256_hash_function = {
    .init = sha3_256_init_wrapper,
    .update = sha3_update_wrapper,
    .final = sha3_final_wrapper,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = SHA3_256_DIGEST_SIZE,
    .name = "SHA3-256"
};

static sha3_hash_function sha3_384_hash_function = {
    .init = sha3_384_init_wrapper,
    .update = sha3_update_wrapper,
    .final = sha3_final_wrapper,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = SHA3_384_DIGEST_SIZE,
    .name = "SHA3-384"
};

static sha3_hash_function sha3_512_hash_function = {
    .init = sha3_512_init_wrapper,
    .update = sha3_update_wrapper,
    .final = sha3_final_wrapper,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = SHA3_512_DIGEST_SIZE,
    .name = "SHA3-512"
};

/* Function declarations from shake.c */
extern int shake128_init(void *context);
extern int shake256_init(void *context);
extern int shake128_final(void *context, void *digest, size_t digest_size);
extern int shake256_final(void *context, void *digest, size_t digest_size);

static sha3_hash_function shake_128_hash_function = {
    .init = shake128_init,
    .update = sha3_update_wrapper,
    .final = shake128_final,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = 0, /* Variable-length output */
    .name = "SHAKE128"
};

static sha3_hash_function shake_256_hash_function = {
    .init = shake256_init,
    .update = sha3_update_wrapper,
    .final = shake256_final,
    .ctx_size = sizeof(sha3_ctx),
    .digest_size = 0, /* Variable-length output */
    .name = "SHAKE256"
};

/* Wrapper function implementations */
static int sha3_224_init_wrapper(void *ctx) {
    return sha3_init((sha3_ctx *)ctx, SHA3_224);
}

static int sha3_256_init_wrapper(void *ctx) {
    return sha3_init((sha3_ctx *)ctx, SHA3_256);
}

static int sha3_384_init_wrapper(void *ctx) {
    return sha3_init((sha3_ctx *)ctx, SHA3_384);
}

static int sha3_512_init_wrapper(void *ctx) {
    return sha3_init((sha3_ctx *)ctx, SHA3_512);
}

static int sha3_update_wrapper(void *ctx, const void *data, size_t len) {
    return sha3_update((sha3_ctx *)ctx, data, len);
}

static int sha3_final_wrapper(void *ctx, void *digest, size_t digest_size) {
    return sha3_final((sha3_ctx *)ctx, digest, digest_size);
}

/* Get hash function instance by type */
const sha3_hash_function* sha3_get_hash_function(sha3_hash_type type) {
    switch (type) {
        case SHA3_224:
            return &sha3_224_hash_function;
        case SHA3_256:
            return &sha3_256_hash_function;
        case SHA3_384:
            return &sha3_384_hash_function;
        case SHA3_512:
            return &sha3_512_hash_function;
        case SHAKE_128:
            return &shake_128_hash_function;
        case SHAKE_256:
            return &shake_256_hash_function;
        default:
            return NULL;
    }
}

/* Create a new hash function instance */
sha3_hash_function* sha3_create_hash_function(
    const char *name,
    size_t ctx_size,
    size_t digest_size,
    int (*init)(void *ctx),
    int (*update)(void *ctx, const void *data, size_t len),
    int (*final)(void *ctx, void *digest, size_t digest_size)
) {
    sha3_hash_function *hash_func;
    char *name_copy;
    
    if (!name || !init || !update || !final || ctx_size == 0) {
        return NULL;
    }
    
    /* Allocate memory for the hash function */
    hash_func = malloc(sizeof(sha3_hash_function));
    if (!hash_func) {
        return NULL;
    }
    
    /* Allocate memory for the name */
    name_copy = malloc(strlen(name) + 1);
    if (!name_copy) {
        free(hash_func);
        return NULL;
    }
    strcpy(name_copy, name);
    
    /* Set fields */
    hash_func->init = init;
    hash_func->update = update;
    hash_func->final = final;
    hash_func->ctx_size = ctx_size;
    hash_func->digest_size = digest_size;
    hash_func->name = name_copy;
    
    return hash_func;
}

/* Free a hash function instance */
void sha3_free_hash_function(sha3_hash_function *hash_func) {
    if (hash_func) {
        free((void *)hash_func->name);
        free(hash_func);
    }
}