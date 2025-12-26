#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Quick build script for developers
# This builds only the working components to get you started fast

echo "🚀 CMPTR Quick Build"
echo "==================="
echo ""

# Check if build directory exists
if [ -d "build" ]; then
    echo "⚠️  Build directory exists. Clean it? (y/N)"
    read -r response
    if [[ "$response" =~ ^[Yy]$ ]]; then
        echo "🧹 Cleaning build directory..."
        rm -rf build
    fi
fi

# Run the working build configuration
echo "🔨 Building CMPTR with working modules..."
./BUILD_WORKING_CONFIG.sh

echo ""
echo "📚 Next Steps:"
echo "  - Read START_HERE.md for project overview"
echo "  - Read CLAUDE.md for technical details"
echo "  - Try: ./build/bin/compile_time_proof_demo"
echo "  - Explore: ./build/bin/verify_truths"
echo ""
echo "Happy hacking! 🎉"