#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Run all BaseFold verifier component tests

set -e

echo "=== Running BaseFold Verifier Component Tests ==="
echo ""

# Check if tests are built
if [ ! -d "bin" ]; then
    echo "Tests not built. Running build script..."
    ./build_tests.sh
fi

# Run each test
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

run_test() {
    local test_name=$1
    local test_binary="bin/$test_name"
    
    if [ ! -x "$test_binary" ]; then
        echo "Error: $test_binary not found or not executable"
        return 1
    fi
    
    echo "Running $test_name..."
    if $test_binary; then
        echo "✅ $test_name PASSED"
        ((PASSED_TESTS++))
    else
        echo "❌ $test_name FAILED"
        ((FAILED_TESTS++))
    fi
    ((TOTAL_TESTS++))
    echo ""
}

# Run all tests
run_test "test_gf128"
run_test "test_sha3"
run_test "test_merkle"
run_test "test_sumcheck"
run_test "test_fri"
run_test "test_integration"

# Summary
echo "=== Test Summary ==="
echo "Total tests: $TOTAL_TESTS"
echo "Passed: $PASSED_TESTS"
echo "Failed: $FAILED_TESTS"

if [ $FAILED_TESTS -eq 0 ]; then
    echo ""
    echo "✅ All tests passed!"
    exit 0
else
    echo ""
    echo "❌ Some tests failed!"
    exit 1
fi