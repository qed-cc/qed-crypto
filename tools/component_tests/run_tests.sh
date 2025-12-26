#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Component test runner for BaseFold verifier circuit

set -e

echo "BaseFold Verifier Circuit Component Test Suite"
echo "=============================================="
echo ""

# Check if we're in the right directory
if [ ! -f "Makefile" ]; then
    echo "Error: Must run from component_tests directory"
    exit 1
fi

# Check if libraries are built
if [ ! -f "../../build/lib/libgf128.a" ] || [ ! -f "../../build/lib/libsha3.a" ]; then
    echo "Error: Required libraries not found. Please build the project first."
    echo "Run: cd ../.. && mkdir -p build && cd build && cmake .. && make"
    exit 1
fi

# Clean previous test artifacts
echo "Cleaning previous test artifacts..."
make clean

# Build all tests
echo "Building component tests..."
make all

echo ""
echo "Running component tests..."
echo "========================="

# Track overall results
TOTAL_TESTS=0
FAILED_TESTS=0

# Run each test and capture results
for test in test_gf128 test_sha3 test_merkle test_sumcheck test_fri; do
    echo ""
    echo ">>> Running $test"
    echo "-------------------"
    
    if ./$test; then
        echo "✓ $test passed"
    else
        echo "✗ $test FAILED"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
done

echo ""
echo "========================="
echo "Test Summary:"
echo "  Total test suites: $TOTAL_TESTS"
echo "  Passed: $((TOTAL_TESTS - FAILED_TESTS))"
echo "  Failed: $FAILED_TESTS"

if [ $FAILED_TESTS -eq 0 ]; then
    echo ""
    echo "✓ All tests passed!"
    exit 0
else
    echo ""
    echo "✗ Some tests failed!"
    exit 1
fi