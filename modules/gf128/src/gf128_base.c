#include "gf128.h"

gf128_t gf128_mul_base(gf128_t a, gf128_t b) {
    gf128_t Z = {0, 0};
    gf128_t V = a;

    for (int i = 0; i < 128; i++) {
        /* If the LSB of b is set, XOR Z with V */
        if (b.lo & 1) {
            Z.hi ^= V.hi;
            Z.lo ^= V.lo;
        }
        /* Record MSB of V before shifting */
        int msb = (int)(V.hi >> 63);
        /* Multiply V by x: shift left by 1 */
        V.hi = (V.hi << 1) | (V.lo >> 63);
        V.lo <<= 1;
        /* If MSB was 1, apply reduction polynomial (0x87) */
        if (msb) {
            V.lo ^= 0x87;
        }
        /* Shift b right by 1 to process the next bit */
        b.lo = (b.lo >> 1) | (b.hi << 63);
        b.hi >>= 1;
    }
    return Z;
}