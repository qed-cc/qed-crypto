#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# build_coverage.sh - Build Gate Computer with code coverage enabled

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "==== Building Gate Computer with Code Coverage ===="
echo "Project root: $PROJECT_ROOT"

# Check for required tools
check_tool() {
    if ! command -v "$1" &> /dev/null; then
        echo "ERROR: $1 is not installed. Please install it first."
        echo "  On Ubuntu/Debian: sudo apt-get install lcov"
        echo "  On openSUSE: sudo zypper install lcov"
        echo "  On macOS: brew install lcov"
        exit 1
    fi
}

check_tool gcov
check_tool lcov
check_tool genhtml

# Clean previous build
echo "Cleaning previous build..."
rm -rf "$PROJECT_ROOT/build_coverage"

# Create build directory
mkdir -p "$PROJECT_ROOT/build_coverage"
cd "$PROJECT_ROOT/build_coverage"

# Configure with coverage
echo "Configuring with coverage enabled..."
cmake .. \
    -DCMAKE_BUILD_TYPE=Coverage \
    -DBUILD_TESTS=ON \
    -DENABLE_COVERAGE=ON \
    -DCMAKE_C_COMPILER=gcc \
    -DCMAKE_CXX_COMPILER=g++

# Build
echo "Building..."
make -j$(nproc)

echo ""
echo "==== Build Complete ===="
echo "To run coverage analysis:"
echo "  cd $PROJECT_ROOT/build_coverage"
echo "  make coverage"
echo ""
echo "To view the report:"
echo "  make coverage-view"
echo ""
echo "Coverage report will be in: $PROJECT_ROOT/build_coverage/coverage/html/index.html"