#include "gf128.h"
/* Inversion of zero returns zero for consistency; division by zero also returns zero. */

// Inversion uses generic multiply that selects the fastest available backend

/**
 * Compute multiplicative inverse in GF(2^128) using exponentiation:
 * a^(2^128-2) = a^(111...110)_2
 */
gf128_t gf128_inv(gf128_t a) {
    // Return zero for input zero
    if (a.hi == 0 && a.lo == 0) {
        return gf128_zero();
    }
    // Exponent = 2^128 - 2 = 0xFF..FFFE; use fixed 4-bit sliding-window exponentiation
    // Precompute table T[k] = a^k for k = 0..15
    gf128_t T[16];
    T[0] = gf128_one();
    T[1] = a;
    for (int k = 2; k < 16; k++) {
        T[k] = gf128_mul(T[k-1], a);
    }
    // Process the 32 nibbles (4-bit windows) of the exponent from MS nibble down to LS nibble
    // Exponent in hex: 0xFF,0xFF,...,0xFF,0xFE (32 bytes -> 16 bytes = 32 nibbles)
    // MS nibble index 0 = 0xF, LS nibble index 31 = 0xE
    gf128_t result = T[0xF];
    for (int i = 1; i < 32; i++) {
        // Square result 4 times (result <<= 4 bits in exponent)
        result = gf128_mul(result, result);
        result = gf128_mul(result, result);
        result = gf128_mul(result, result);
        result = gf128_mul(result, result);
        // Multiply by T[nibble]
        uint8_t nib = (i == 31 ? 0xE : 0xF);
        result = gf128_mul(result, T[nib]);
    }
    return result;
}

/**
 * Divide elements in GF(2^128): a / b = a * inv(b)
 */
gf128_t gf128_div(gf128_t a, gf128_t b) {
    // Handle division by zero: defined to be zero
    if (b.hi == 0 && b.lo == 0) {
        return (gf128_t){0, 0};
    }
    gf128_t invb = gf128_inv(b);
    return gf128_mul(a, invb);
}