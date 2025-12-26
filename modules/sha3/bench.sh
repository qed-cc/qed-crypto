#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2025 Rhett Creighton
set -euo pipefail

#---------------------------------------------------------------------
# Simple all-in-one script to build, test, and benchmark SHA3/Merkle lib
# Supports AVX-512 for high performance on x86_64
# Usage: ./bench.sh [PAR_BENCH_COUNT] [MERKLE_BENCH_LEAVES]
#   Defaults: PAR_BENCH_COUNT=10000000, MERKLE_BENCH_LEAVES=10000000
# Override via env: BUILD_DIR, PAR_BENCH_COUNT, MERKLE_BENCH_LEAVES
#---------------------------------------------------------------------

# Check for AVX-512 support
if ! grep -q avx512f /proc/cpuinfo; then
  echo "Warning: CPU does not report AVX-512 (avx512f). Performance may be suboptimal."
fi

# Default parameters (can be overridden via env)
BUILD_DIR=${BUILD_DIR:-build}
PAR_BENCH_COUNT=${PAR_BENCH_COUNT:-10000000}
MERKLE_BENCH_LEAVES=${MERKLE_BENCH_LEAVES:-10000000}

# Override via args
if [ "$#" -ge 1 ]; then PAR_BENCH_COUNT=$1; fi
if [ "$#" -ge 2 ]; then MERKLE_BENCH_LEAVES=$2; fi

echo "=== Building library and examples ==="
mkdir -p "$BUILD_DIR"
pushd "$BUILD_DIR" > /dev/null
cmake -DCMAKE_BUILD_TYPE=Release -DSHA3_BUILD_EXAMPLES=ON ..
make -j"$(nproc)"
popd > /dev/null

echo "=== Running self-tests ==="
"$BUILD_DIR/test_sha3"
"$BUILD_DIR/test_merkle"

echo "=== SHA3 Parallel Benchmark ==="
"$BUILD_DIR/bin/sha3_parallel_benchmark" "$PAR_BENCH_COUNT"

echo "=== Merkle Tree Benchmark ==="
"$BUILD_DIR/bin/sha3_merkle_benchmark" "$MERKLE_BENCH_LEAVES"

echo "All done."