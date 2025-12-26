#!/bin/bash
# Gate Computer App Build Script
# This script builds the Gate Computer application with all targets
#
# Usage: ./build.sh [make-target]
# Example: ./build.sh gate_computer
# Example: ./build.sh gate_computer_final_sha3_impl_test

# Exit on any error
set -e

# Ensure we're in the correct directory
SCRIPT_DIR="$(dirname "$0")"
cd "$SCRIPT_DIR"

# Create build directory if it doesn't exist
mkdir -p build

# Navigate to build directory
cd build
# Use build directory for temporary files to avoid /tmp permission issues
export TMPDIR="$PWD"

# Run cmake to generate build files
echo "Generating build files..."
cmake ..

# Build specified target or all targets if none specified
if [ $# -gt 0 ]; then
    echo "Building target: $1"
    make "$1"
else
    echo "Building all targets..."
    make
fi

echo "Build complete."
echo "Executables are in the build/ directory"