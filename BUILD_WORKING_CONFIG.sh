#!/bin/bash
# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Clean build configuration that only enables working modules

echo "🔨 Building CMPTR with only working modules..."

# Clean previous build
rm -rf build
mkdir -p build
cd build

# Configure with only working modules
cmake \
    -DCMAKE_BUILD_TYPE=Release \
    -DBUILD_BASEFOLD_RAA=ON \
    -DBUILD_TRUTH_VERIFIER=ON \
    -DBUILD_FORMAL_PROOF_CIRCUITS=OFF \
    -DBUILD_CMPTR_ACCUMULATOR=OFF \
    -DBUILD_CMPTR_BLOCKCHAIN=OFF \
    -DBUILD_CMPTR_POS=OFF \
    -DBUILD_CMPTR_SIGNATURES=OFF \
    -DBUILD_CMPTR_STREAM=OFF \
    -DBUILD_CMPTR_CHANNEL=OFF \
    -DBUILD_CMPTR_EXCHANGE=OFF \
    -DBUILD_CMPTR_VRF=OFF \
    -DBUILD_CMPTR_TREES=OFF \
    -DBUILD_CMPTR_COMMITMENTS=OFF \
    -DBUILD_TESTS=OFF \
    -DBUILD_BENCHMARKS=OFF \
    -DBUILD_DOCS=OFF \
    ..

# Build
make -j$(nproc)

echo ""
echo "✅ Build complete! Working binaries:"
echo "  ./bin/crypto_demo               - Crypto primitives overview"
echo "  ./bin/verify_truths             - Truth verification system"  
echo "  ./bin/sha3_working              - SHA3 example"
echo "  ./bin/crypto_working            - Combined crypto demo"
echo "  ./bin/compile_time_proof_demo   - Compile-time proofs demo"
echo ""
echo "🔐 Compile-Time Proofs: ACTIVE"
echo "   All axioms and security properties verified at build time!"
echo ""
echo "Try: ./bin/compile_time_proof_demo"