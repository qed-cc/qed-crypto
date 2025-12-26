#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Real SHA-2 Proof System Comparison - One Command Demo
# Builds and runs comprehensive comparison between BaseFold and Groth16

set -e  # Exit on any error

echo "🚀 Real SHA-2 Proof System Comparison"
echo "======================================"
echo ""
echo "This demo will compare cryptographically secure SHA-2 proofs:"
echo "• BaseFold: Post-quantum SHA3-256 (192K gates, ~65KB proofs)"
echo "• Groth16: Pre-quantum SHA-256 (87K constraints, 256 byte proofs)"
echo ""

# Build the comparison demo
echo "📦 Building SHA-2 comparison demo..."
cd /home/bob/github/gate_computer
gcc -o sha2_comparison_demo sha2_comparison_demo.c -std=c99

# Ensure BaseFold is built
echo "🔧 Ensuring BaseFold system is built..."
if [ ! -f "build/bin/gate_computer" ]; then
    echo "Building BaseFold system..."
    mkdir -p build
    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Release
    make -j$(nproc) gate_computer
    cd ..
fi

# Ensure Groth16 is built  
echo "🔧 Ensuring Groth16 system is built..."
cd modules/groth16_production
if [ ! -d "build" ]; then
    mkdir -p build
fi
cd build
if [ ! -f "examples/bitcoin_demo" ]; then
    echo "Building Groth16 production system..."
    cmake .. -DCMAKE_BUILD_TYPE=Release
    make -j$(nproc)
fi
cd ../../..

echo "✅ Build complete! Running real SHA-2 comparison..."
echo ""

# Run the comparison
./sha2_comparison_demo

echo ""
echo "🏁 Real SHA-2 comparison completed!"
echo ""
echo "📋 Summary of what was tested:"
echo "   • BaseFold: Real SHA3-256 circuit with 192,086 gates"
echo "   • Groth16: Real SHA-256 circuit with 87,626 constraints"
echo "   • Both systems proved knowledge of hash preimage"
echo "   • Performance, proof size, and security compared"
echo ""
echo "🎯 Key insight: Both systems provide real cryptographic security!"
echo "   • Choose BaseFold for quantum resistance"
echo "   • Choose Groth16 for compact proofs and fast verification"