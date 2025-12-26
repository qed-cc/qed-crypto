/*
 * Table-driven multiplication using 8-bit (byte) lookup and Horner's method.
 * Builds a 256-entry table per multiply; suitable for performance-optimized use.
 */
/* Table-driven multiplication using 8-bit (byte) lookup and Horner's method */
#include "gf128.h"
/* Forward declaration for pow8 helper */
static inline gf128_t gf128_mul_pow8(gf128_t v);
/* Multiply v by x in GF(2^128) (polynomial: x^128 + x^7 + x^2 + x + 1) */
static inline gf128_t gf128_mul_x(gf128_t v) {
    int msb = (int)(v.hi >> 63);
    uint64_t hi = (v.hi << 1) | (v.lo >> 63);
    uint64_t lo = v.lo << 1;
    if (msb) lo ^= 0x87;
    return (gf128_t){hi, lo};
}
/* Precomputed table (256 entries) context operations */
void gf128_table256_init(gf128_table256_t *ctx, gf128_t a) {
    ctx->tbl[0] = (gf128_t){0, 0};
    /* Initialize entry for 1 */
    ctx->tbl[1] = a;
    /* Build table by successive doubling and XOR: a*c for c = 2..255 */
    for (int c = 2; c < 256; c++) {
        if ((c & 1) == 0) {
            /* even: multiply previous half-entry by x */
            ctx->tbl[c] = gf128_mul_x(ctx->tbl[c >> 1]);
        } else {
            /* odd: tbl[c] = tbl[c-1] XOR a */
            ctx->tbl[c].hi = ctx->tbl[c-1].hi ^ a.hi;
            ctx->tbl[c].lo = ctx->tbl[c-1].lo ^ a.lo;
        }
    }
}
gf128_t gf128_mul_table256(const gf128_table256_t *ctx, gf128_t b) {
    gf128_t r = {0, 0};
    for (int j = 15; j >= 0; j--) {
        r = gf128_mul_pow8(r);
        uint8_t byte;
        if (j < 8)
            byte = (uint8_t)((b.lo >> (8 * j)) & 0xFF);
        else
            byte = (uint8_t)((b.hi >> (8 * (j - 8))) & 0xFF);
        r.hi ^= ctx->tbl[byte].hi;
        r.lo ^= ctx->tbl[byte].lo;
    }
    return r;
}

/* Multiply v by x^8 in GF(2^128) using the reduction polynomial x^128 = x^7 + x^2 + x + 1 */
static inline gf128_t gf128_mul_pow8(gf128_t v) {
    uint64_t hi = v.hi;
    uint64_t lo = v.lo;
    /* Overflow bits when shifting left by 8 */
    uint8_t cb = (uint8_t)(hi >> 56);
    /* Shift left 8 bits across 128-bit value */
    uint64_t new_hi = (hi << 8) | (lo >> 56);
    uint64_t new_lo = lo << 8;
    /* Fold overflow bits via polynomial 0x87 (unrolled) */
    if (cb & (1U << 0)) new_lo ^= (uint64_t)0x87ULL << 0;
    if (cb & (1U << 1)) new_lo ^= (uint64_t)0x87ULL << 1;
    if (cb & (1U << 2)) new_lo ^= (uint64_t)0x87ULL << 2;
    if (cb & (1U << 3)) new_lo ^= (uint64_t)0x87ULL << 3;
    if (cb & (1U << 4)) new_lo ^= (uint64_t)0x87ULL << 4;
    if (cb & (1U << 5)) new_lo ^= (uint64_t)0x87ULL << 5;
    if (cb & (1U << 6)) new_lo ^= (uint64_t)0x87ULL << 6;
    if (cb & (1U << 7)) new_lo ^= (uint64_t)0x87ULL << 7;
    return (gf128_t){new_hi, new_lo};
}

gf128_t gf128_mul_table(gf128_t a, gf128_t b) {
    /* Build table of a * c for c = 0..255 by successive doubling and XOR */
    gf128_t tbl[256];
    tbl[0] = (gf128_t){0, 0};
    tbl[1] = a;
    for (int c = 2; c < 256; c++) {
        if ((c & 1) == 0) {
            tbl[c] = gf128_mul_x(tbl[c >> 1]);
        } else {
            tbl[c].hi = tbl[c-1].hi ^ a.hi;
            tbl[c].lo = tbl[c-1].lo ^ a.lo;
        }
    }
    /* Horner's method: fold in each byte of b */
    gf128_t r = {0, 0};
    for (int j = 15; j >= 0; j--) {
        /* Multiply accumulator by x^8 */
        r = gf128_mul_pow8(r);
        /* Extract byte j from b */
        uint8_t byte;
        if (j < 8)
            byte = (uint8_t)((b.lo >> (8 * j)) & 0xFF);
        else
            byte = (uint8_t)((b.hi >> (8 * (j - 8))) & 0xFF);
        /* XOR in partial product */
        r.hi ^= tbl[byte].hi;
        r.lo ^= tbl[byte].lo;
    }
    return r;
}