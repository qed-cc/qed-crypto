#ifndef GF128_H
#define GF128_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    uint64_t hi;
    uint64_t lo;
} gf128_t;

/* Add two field elements: bitwise XOR */
static inline gf128_t gf128_add(gf128_t a, gf128_t b) {
    gf128_t r = {a.hi ^ b.hi, a.lo ^ b.lo};
    return r;
}
#ifdef USE_GFNI
/**
 * Runtime check for GFNI support (x86/x86_64)
 * GFNI requires AVX-512GFNI and AVX-512VBMI for reduction instructions.
 */
static inline bool gf128_has_gfni(void) {
#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__i386__)
    return __builtin_cpu_supports("gfni") && __builtin_cpu_supports("avx512vbmi");
#endif
#endif
    return false;
}
#endif
/* Constants: zero and one elements */
static inline gf128_t gf128_zero(void) { return (gf128_t){0, 0}; }
static inline gf128_t gf128_one(void)  { return (gf128_t){0, 1}; }

/* Construct from big-endian 16-byte array */
static inline gf128_t gf128_from_be(const uint8_t b[16]) {
    gf128_t r;
    r.hi = ((uint64_t)b[0] << 56) | ((uint64_t)b[1] << 48) | ((uint64_t)b[2] << 40) | ((uint64_t)b[3] << 32)
         | ((uint64_t)b[4] << 24) | ((uint64_t)b[5] << 16) | ((uint64_t)b[6] <<  8) |  (uint64_t)b[7];
    r.lo = ((uint64_t)b[8] << 56) | ((uint64_t)b[9] << 48) | ((uint64_t)b[10] << 40)| ((uint64_t)b[11] << 32)
         | ((uint64_t)b[12] << 24)| ((uint64_t)b[13] << 16)| ((uint64_t)b[14] <<  8)|  (uint64_t)b[15];
    return r;
}

/* Serialize to big-endian 16-byte array */
static inline void gf128_to_be(gf128_t a, uint8_t b[16]) {
    b[0] = (uint8_t)(a.hi >> 56);
    b[1] = (uint8_t)(a.hi >> 48);
    b[2] = (uint8_t)(a.hi >> 40);
    b[3] = (uint8_t)(a.hi >> 32);
    b[4] = (uint8_t)(a.hi >> 24);
    b[5] = (uint8_t)(a.hi >> 16);
    b[6] = (uint8_t)(a.hi >>  8);
    b[7] = (uint8_t)(a.hi      );
    b[8] = (uint8_t)(a.lo >> 56);
    b[9] = (uint8_t)(a.lo >> 48);
    b[10] = (uint8_t)(a.lo >> 40);
    b[11] = (uint8_t)(a.lo >> 32);
    b[12] = (uint8_t)(a.lo >> 24);
    b[13] = (uint8_t)(a.lo >> 16);
    b[14] = (uint8_t)(a.lo >>  8);
    b[15] = (uint8_t)(a.lo      );
}
/* Construct from little-endian 16-byte array */
static inline gf128_t gf128_from_le(const uint8_t b[16]) {
    gf128_t r;
    r.lo = ((uint64_t)b[0])        | ((uint64_t)b[1] << 8)  | ((uint64_t)b[2] << 16) | ((uint64_t)b[3] << 24)
         | ((uint64_t)b[4] << 32) | ((uint64_t)b[5] << 40) | ((uint64_t)b[6] << 48) | ((uint64_t)b[7] << 56);
    r.hi = ((uint64_t)b[8])        | ((uint64_t)b[9] << 8)  | ((uint64_t)b[10] << 16)| ((uint64_t)b[11] << 24)
         | ((uint64_t)b[12] << 32)| ((uint64_t)b[13] << 40)| ((uint64_t)b[14] << 48)| ((uint64_t)b[15] << 56);
    return r;
}
/* Serialize to little-endian 16-byte array */
static inline void gf128_to_le(gf128_t a, uint8_t b[16]) {
    b[0] = (uint8_t)(a.lo      );
    b[1] = (uint8_t)(a.lo >> 8 );
    b[2] = (uint8_t)(a.lo >> 16);
    b[3] = (uint8_t)(a.lo >> 24);
    b[4] = (uint8_t)(a.lo >> 32);
    b[5] = (uint8_t)(a.lo >> 40);
    b[6] = (uint8_t)(a.lo >> 48);
    b[7] = (uint8_t)(a.lo >> 56);
    b[8] = (uint8_t)(a.hi      );
    b[9] = (uint8_t)(a.hi >> 8 );
    b[10] = (uint8_t)(a.hi >> 16);
    b[11] = (uint8_t)(a.hi >> 24);
    b[12] = (uint8_t)(a.hi >> 32);
    b[13] = (uint8_t)(a.hi >> 40);
    b[14] = (uint8_t)(a.hi >> 48);
    b[15] = (uint8_t)(a.hi >> 56);
}
/**
 * @brief Canonical byte conversion helpers for basefold integration
 * 
 * These functions provide a consistent interface for converting between
 * GF(2^128) elements and byte arrays, abstracting the endianness details.
 * Used by basefold proof system for mask generation and field element handling.
 */
static inline gf128_t gf128_from_bytes(const uint8_t b[16]) {
    return gf128_from_le(b);
}
static inline void gf128_to_bytes(gf128_t a, uint8_t out[16]) {
    gf128_to_le(a, out);
}

/* Equality and zero checks */
static inline bool gf128_is_zero(gf128_t a) {
    return (a.hi == 0) && (a.lo == 0);
}
static inline bool gf128_eq(gf128_t a, gf128_t b) {
    return (a.hi == b.hi) && (a.lo == b.lo);
}

/* Multiply a and b using naive bitwise (reference) algorithm */
gf128_t gf128_mul_base(gf128_t a, gf128_t b);

/* Table-driven multiplication using 8-bit (byte) lookup table */
gf128_t gf128_mul_table(gf128_t a, gf128_t b);
/* Context for optimized 8-bit table-driven multiplication */
typedef struct { gf128_t tbl[256]; } gf128_table256_t;
/* Initialize the 8-bit table context for multiplies by 'a' */
void gf128_table256_init(gf128_table256_t *ctx, gf128_t a);
/* Multiply using precomputed 8-bit table context */
gf128_t gf128_mul_table256(const gf128_table256_t *ctx, gf128_t b);

/* One-to-many multiply context: optimize repeated multiplies by same a */
typedef struct {
    gf128_table256_t tbl;
} gf128_mul_ctx_t;
/**
 * Initialize a multiply context for element a (precomputes 8-bit table).
 */
static inline void gf128_mul_ctx_init(gf128_mul_ctx_t *ctx, gf128_t a) {
    gf128_table256_init(&ctx->tbl, a);
}
/**
 * Multiply b by the context-initialized element.
 */
static inline gf128_t gf128_mul_ctx_mul(const gf128_mul_ctx_t *ctx, gf128_t b) {
    return gf128_mul_table256(&ctx->tbl, b);
}

/* PCLMUL-based multiplication: uses hardware CLMUL when enabled, else fall back to table-driven */
/* PCLMUL-based multiplication (dynamic dispatch when available) */
#ifdef ENABLE_PCLMUL
gf128_t gf128_mul_pclmul(gf128_t a, gf128_t b);
#else
static inline gf128_t gf128_mul_pclmul(gf128_t a, gf128_t b) {
    return gf128_mul_table(a, b);
}
#endif
/* Optional Karatsuba-based PCLMUL: uses 3 CLMULs per multiply instead of 4 */
#ifdef USE_PCLMUL_KARATSUBA
gf128_t gf128_mul_pclmul_kara(gf128_t a, gf128_t b);
#endif

/* Runtime check for carry-less multiply support */
static inline bool gf128_has_pclmul(void) {
    #if defined(__GNUC__) || defined(__clang__)
        /* x86 PCLMUL or ARM PMULL */
        #if defined(__x86_64__) || defined(__i386__)
            if (__builtin_cpu_supports("pclmul")) return true;
        #elif defined(__aarch64__) || defined(__arm__)
            if (__builtin_cpu_supports("pmull")) return true;
        #else
            return false;
        #endif
        return false;
    #else
        #ifdef ENABLE_PCLMUL
            return true;
        #else
            return false;
        #endif
    #endif
}
// Runtime check for AVX2 + PCLMUL support (x86/x86_64)
static inline bool gf128_has_avx2(void) {
#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__i386__)
    return __builtin_cpu_supports("avx2") && __builtin_cpu_supports("pclmul");
#endif
#endif
    return false; // Default false if no specific check available
}

// Runtime check for AVX-512 + VPCLMULQDQ support (x86/x86_64)
static inline bool gf128_has_avx512(void) {
    #if defined(__GNUC__) || defined(__clang__)
    #if defined(__x86_64__) || defined(__i386__)
        return __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512dq") && \
               __builtin_cpu_supports("avx512vl") && __builtin_cpu_supports("avx512bw") && \
               __builtin_cpu_supports("pclmul");
    #endif
    #endif
    return false; // Default false if no specific check available
}

/* Generic multiply: dispatched at library initialization to fastest backend */
/* Returns a * b using hardware-accelerated or table-driven implementation */
gf128_t gf128_mul(gf128_t a, gf128_t b);

/* Inversion and division */
/**
 * Compute multiplicative inverse in GF(2^128) using exponentiation (a^(2^128-2)).
 */
gf128_t gf128_inv(gf128_t a);
/**
 * Divide elements in GF(2^128): a * inv(b)
 */
gf128_t gf128_div(gf128_t a, gf128_t b);

/* Optional AVX2-accelerated PCLMUL variants */
#ifdef USE_AVX2
/**
 * Batched 2-way AVX2 PCLMUL multiply: out[i] = a[i] * b[i] for i=0..1
 */
void gf128_mul2_pclmul_avx2(const gf128_t a[2], const gf128_t b[2], gf128_t out[2]);
/**
 * Scalar AVX2 wrapper: uses two-way batched AVX2 PCLMUL.
 */
gf128_t gf128_mul_pclmul_avx2(gf128_t a, gf128_t b);
#endif

/* Optional AVX-512 accelerated PCLMUL variants */
 #ifdef USE_AVX512
 /**
  * Batched 4-way AVX-512 VPCLMULQDQ multiply: out[i] = a[i] * b[i] for i=0..3
  */
 void gf128_mul4_pclmul_avx512(const gf128_t a[4], const gf128_t b[4], gf128_t out[4]);
 /**
  * Scalar AVX-512 wrapper: uses four-way batched AVX-512 VPCLMULQDQ.
  */
 gf128_t gf128_mul_pclmul_avx512(gf128_t a, gf128_t b);
 /**
  * Super-batched 8-way AVX-512 PCLMUL multiply: interleaves two 4-way batches to hide latency
  * out[i] = a[i] * b[i] for i=0..7
  */
 void gf128_mul8_pclmul_avx512_super(const gf128_t a[8], const gf128_t b[8], gf128_t out[8]);
 #endif
 /* Experimental GFNI-only multiplication kernel */
 #ifdef USE_GFNI_MUL
 gf128_t gf128_mul_gfni(gf128_t a, gf128_t b);
 #endif

#ifdef __cplusplus
}
#endif

#endif /* GF128_H */