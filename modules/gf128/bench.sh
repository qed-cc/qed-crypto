#!/usr/bin/env bash
set -euo pipefail
# bench.sh: one-line build & benchmark script for GF128 library
## bench.sh: configure, build, and run GF128 multiply benchmarks quietly
rm -rf build && mkdir build && cd build
echo
echo "==> Configuring and building bench_mul (this may take a few seconds)..."
# Suppress CMake warnings and build output
cmake -Wno-dev -DCMAKE_BUILD_TYPE=Release \
      -DUSE_PCLMUL=ON \
      -DUSE_PCLMUL_KARATSUBA=ON \
      -DUSE_AVX2=ON \
      -DUSE_AVX512=ON \
      -DUSE_GFNI=ON \
      -DENABLE_MICROTUNE=ON .. > /dev/null 2>&1
cmake --build . --target bench_mul --parallel > /dev/null 2>&1

echo
echo "==> Single-threaded GF(2^128) multiply throughput (Mops/sec)"
# Skip CSV header, sort by throughput, and format
./benchmarks/bench_mul --csv | tail -n +2 | sort -t, -k2 -nr | \
  awk -F, '{ printf("%-30s %8.2f\n", $1, $2) }'

echo
echo "==> Multi-threaded GF(2^128) multiply throughput (all $(nproc) cores, Mops/sec)"
./benchmarks/bench_mul --threads $(nproc) --csv | tail -n +2 | sort -t, -k2 -nr | \
  awk -F, '{ printf("%-30s %8.2f\n", $1, $2) }'