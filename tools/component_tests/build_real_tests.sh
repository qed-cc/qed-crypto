#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Build script for BaseFold verifier component tests with real libraries

set -e

echo "Building BaseFold verifier component tests with real libraries..."

# Use the optimized build directory
BUILD_DIR="../../build_opt"

# Verify libraries exist
if [ ! -f "$BUILD_DIR/lib/libgf128.a" ] || [ ! -f "$BUILD_DIR/lib/libsha3.a" ]; then
    echo "Error: Required libraries not found. Building them now..."
    cd ../..
    if [ ! -d "build_opt" ]; then
        mkdir -p build_opt
    fi
    cd build_opt
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make gf128 sha3
    cd -
fi

# Create output directory
mkdir -p bin

# Common flags
INCLUDES="-I../../modules/gf128/include -I../../modules/sha3/include"
LIBS="-L$BUILD_DIR/lib"
CFLAGS="-O2 -Wall -Wextra -std=c99"

# Build GF128 test
echo "Building test_gf128_real..."
gcc $CFLAGS $INCLUDES test_gf128_real.c -o bin/test_gf128_real $LIBS -lgf128 -lm

# Build SHA3 test (SHA3 requires OpenSSL)
echo "Building test_sha3_real..."
gcc $CFLAGS $INCLUDES test_sha3_real.c -o bin/test_sha3_real $LIBS -lsha3 -lcrypto

echo ""
echo "Real library tests built successfully!"
echo ""
echo "To run tests:"
echo "  ./bin/test_gf128_real"
echo "  ./bin/test_sha3_real"