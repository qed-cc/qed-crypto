#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Build script for BaseFold verifier component tests

set -e

echo "Building BaseFold verifier component tests..."

# Determine the build directory to use
BUILD_DIR="../../build_opt"
if [ ! -d "$BUILD_DIR/lib" ]; then
    echo "Error: Build directory not found. Please build the project first."
    echo "Run: cd ../.. && mkdir -p build_opt && cd build_opt && cmake .. && make"
    exit 1
fi

# Check for required libraries
if [ ! -f "$BUILD_DIR/lib/libgf128.a" ]; then
    echo "Error: libgf128.a not found in $BUILD_DIR/lib/"
    exit 1
fi

if [ ! -f "$BUILD_DIR/lib/libsha3.a" ]; then
    echo "Error: libsha3.a not found in $BUILD_DIR/lib/"
    exit 1
fi

echo "Found required libraries in $BUILD_DIR/lib/"

# Create output directory
mkdir -p bin

# Common includes and libraries
INCLUDES="-I../../modules/gf128/include -I../../modules/sha3/include -I../../modules/basefold/include -I../../include"
LIBS="-L$BUILD_DIR/lib -lgf128 -lsha3 -lm"
CFLAGS="-O2 -Wall -Wextra -std=c99"

# Build each test
echo "Building test_gf128..."
gcc $CFLAGS $INCLUDES test_gf128.c -o bin/test_gf128 $LIBS

echo "Building test_sha3..."
gcc $CFLAGS $INCLUDES test_sha3.c -o bin/test_sha3 $LIBS

echo "Building test_merkle..."
gcc $CFLAGS $INCLUDES test_merkle.c -o bin/test_merkle $LIBS

echo "Building test_sumcheck..."
gcc $CFLAGS $INCLUDES test_sumcheck.c -o bin/test_sumcheck $LIBS

echo "Building test_fri..."
gcc $CFLAGS $INCLUDES test_fri.c -o bin/test_fri $LIBS

echo "Building test_integration..."
gcc $CFLAGS $INCLUDES test_integration.c -o bin/test_integration $LIBS

echo ""
echo "All tests built successfully!"
echo ""
echo "To run tests:"
echo "  ./bin/test_gf128"
echo "  ./bin/test_sha3"
echo "  ./bin/test_merkle"
echo "  ./bin/test_sumcheck"
echo "  ./bin/test_fri"
echo "  ./bin/test_integration"
echo ""
echo "Or run all tests:"
echo "  ./run_all_tests.sh"