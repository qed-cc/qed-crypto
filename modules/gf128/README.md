<!-- README.md for GF128 Arithmetic Library -->
# GF128 C99 Library

[![CI](https://github.com/RhettCreighton/gf128/actions/workflows/ci.yml/badge.svg)](https://github.com/RhettCreighton/gf128/actions)

A high-performance finite field GF(2^128) arithmetic library in C99, featuring multiple optimized multiplication implementations and automatic runtime dispatch.

## Features
- Bitwise reference implementation (gf128_mul_base)
- Table-driven multiplication (gf128_mul_table)
- Hardware-accelerated PCLMUL intrinsic path (gf128_mul_pclmul)
- Karatsuba optimization (3 CLMULs)
- AVX2 2-way batched PCLMUL
- AVX-512 4-way and 8-way super-batched PCLMUL
- GFNI-accelerated reduction
- Runtime dispatch (`gf128_mul`) and hardware checks
- CMake package export for easy integration
- Unit tests and benchmarks

## Installation
```sh
git clone https://github.com/RhettCreighton/gf128.git
cd gf128
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DUSE_AVX2=ON \
      -DUSE_AVX512=ON \
      -DUSE_GFNI=ON \
      -DENABLE_MICROTUNE=ON \
      ..
make
sudo make install
```
 
## Quick-Start Benchmark
From a fresh clone, run:
```bash
git clone https://github.com/RhettCreighton/gf128.git \
  && cd gf128 \
  && bash bench.sh
```
This builds all optimized variants (bitwise, table-driven, PCLMUL, AVX2, AVX-512, GFNI) and immediately prints:
- Single-threaded throughput sorted by best performer
- Full core-count (nproc) multi-threaded throughput
No extra flags required — you’ll see the fastest GF(2^128) path on your machine right away.

### Example Output
On a 16-core AVX-512/GFNI-capable machine, `bash bench.sh` yields:
```
==> Single-threaded GF(2^128) multiply throughput (Mops/sec)
gf128_mul8_pclmul_avx512_super      1624.68
gf128_mul4_pclmul_avx512            1450.84
gf128_mul2_pclmul_avx2               380.59
gf128_mul_pclmul_avx2                 91.55
gf128_mul_pclmul_avx512               77.63
gf128_mul_pclmul_kara                 62.87
gf128_mul_pclmul                       4.16
gf128_mul_table                        4.11
gf128_mul                              3.97
gf128_mul_base                         3.28

==> Multi-threaded GF(2^128) multiply throughput (all 16 cores, Mops/sec)
gf128_mul8_pclmul_avx512_super      9626.94
gf128_mul4_pclmul_avx512            1426.01
gf128_mul2_pclmul_avx2               380.23
gf128_mul_pclmul_avx2                 91.51
gf128_mul_pclmul_avx512               76.36
gf128_mul_pclmul_kara                 62.51
gf128_mul                              4.01
gf128_mul_table                        3.99
gf128_mul_pclmul                       3.94
gf128_mul_base                         3.24
```

## CMake Integration
Use the installed package in your CMake project:
```cmake
cmake_minimum_required(VERSION 3.5)
project(myapp C)

find_package(gf128 0.1.0 REQUIRED)

add_executable(myapp main.c)
target_link_libraries(myapp PRIVATE gf128::gf128)
```

## pkg-config Integration

If you prefer pkg-config, the library also installs a `.pc` file. To compile:

```sh
gcc $(pkg-config --cflags --libs gf128) myapp.c -o myapp
```

Control performance variants at configure time:
```sh
cmake -DUSE_AVX2=ON -DUSE_AVX512=ON -DUSE_GFNI=ON -DENABLE_MICROTUNE=ON ..
```

## API Usage
Include the public header:
```c
#include <gf128.h>
```
Basic operations:
```c
gf128_t a = gf128_one();
gf128_t b = gf128_from_be(bytes);
gf128_t c = gf128_mul(a, b); // automatic dispatch to fastest variant
```
Other functions:
- `gf128_add(a, b)` – field addition (XOR)
- `gf128_mul_table(a, b)` – table-driven multiply
- `gf128_mul_pclmul(a, b)` – PCLMUL intrinsic path (or fallback)
- `gf128_mul_pclmul_avx2(a, b)` – AVX2 variant
- `gf128_mul_pclmul_avx512(a, b)` – AVX-512 variant
- Runtime checks: `gf128_has_pclmul()`, `gf128_has_avx2()`, `gf128_has_avx512()`, `gf128_has_gfni()`

## Examples
See `examples/example.c` for usage examples.

## Benchmarks
For a one-line, all-variant quick run (including single- and multi-threaded) use:

```bash
bash bench.sh
```

Alternatively, you can directly use `benchmarks/bench_mul` to measure specific variants; see `codex.md` for detailed instructions.

## Release Notes

See the [CHANGELOG](CHANGELOG.md) for detailed release notes and version history.

## License
Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.