# GF128 Library Design

This document describes the design rationale for the GF128 arithmetic library.

## Irreducible Polynomial

We use the irreducible polynomial
```
x^128 + x^7 + x^2 + x + 1
```
commonly used in GCM (Galois/Counter Mode) of AES.

## Representation

Each field element is represented as a 128-bit value (`gf128_t`)
with two 64-bit limbs: `hi` (most significant bits) and `lo` (least significant bits).

## Multiplication Algorithms

- `gf128_mul_base`: Bitwise reference implementation; shift-and-reduce bit-by-bit.
- `gf128_mul_table`: Table-driven 8-bit (byte) implementation; builds a 256-entry table of `a * c` for c = 0..255, then uses Horner's method over the bytes of `b` with a fast `mul_pow8` shift-and-reduce.
  For high-throughput use, the precomputed context (`gf128_table256_init` + `gf128_mul_table256`) amortizes table construction across multiple operations.
  
- `gf128_mul_pclmul`: Carry-less multiplication using PCLMUL intrinsics; computes the 128×128→256-bit CLMUL product and reduces it modulo the irreducible polynomial.

## API Extensions
- **Big-endian serialization**: `gf128_from_be` / `gf128_to_be` convert between big-endian 16-byte arrays and `gf128_t`.
- **Constants**: `gf128_zero()` / `gf128_one()` for the additive and multiplicative identity.
- **Little-endian serialization**: `gf128_from_le` / `gf128_to_le` for little-endian byte arrays.
- **Comparison**: `gf128_eq(a,b)` for equality, `gf128_is_zero(a)` to test zero.
- **Zero inversion**: `gf128_inv(0)` returns zero (consistent with `gf128_div`).

## Compile-time Feature Detection
- PCLMUL support is detected in CMake via the `-mpclmul` compiler flag; when available, `ENABLE_PCLMUL` enables the optimized path in `gf128_mul_pclmul`.
## Inversion and Division

Routines for inversion (`gf128_inv`) and division (`gf128_div`) use exponentiation: inversion is computed as `a^(2^128 - 2)` via a fixed 4-bit sliding-window algorithm (reducing multiplies by ~2.5× over naive bitwise square-and-multiply), and division is implemented as `a * inv(b)`.
## Performance Tradeoffs

Multiplication implementations vary in throughput and setup cost:

| Implementation      | Throughput (cycles/byte) | Setup Cost                         |
|---------------------|--------------------------|------------------------------------|
| `gf128_mul_base`    | ~200                     | None                               |
| `gf128_mul_table`   | ~20                      | ~1500 cycles (one-time per operand) |
| `gf128_mul_table256`| ~20                      | ~1500 cycles (amortized)           |
| `gf128_mul_pclmul`  | ~2                       | None (requires hardware support)   |

The table-driven implementations incur a cost to build the 256-entry lookup table (approximately 1500 cycles), which is amortized when performing many multiplies with the same operand.  The PCLMUL-based multiply requires CPU support but offers the highest throughput with minimal setup.