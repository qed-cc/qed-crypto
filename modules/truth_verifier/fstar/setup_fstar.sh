#!/bin/bash
# Setup F* for truth bucket formal verification

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$SCRIPT_DIR/../../.."
FSTAR_DIR="$PROJECT_ROOT/vendor/FStar"

echo "=== F* Setup for Truth Bucket Formal Verification ==="
echo

# Check if F* is cloned
if [ ! -d "$FSTAR_DIR" ]; then
    echo "ERROR: F* not found at $FSTAR_DIR"
    echo "Please clone it first: git clone https://github.com/FStarLang/FStar.git vendor/FStar"
    exit 1
fi

# Build F* if not already built
if [ ! -f "$FSTAR_DIR/bin/fstar.exe" ]; then
    echo "Building F*..."
    cd "$FSTAR_DIR"
    make -j$(nproc) || {
        echo "ERROR: F* build failed"
        echo "You may need to install dependencies:"
        echo "  - OCaml >= 4.08"
        echo "  - OPAM packages: batteries, zarith, stdint, yojson, fileutils, pprint, sedlex, ppxlib, ppx_deriving, ppx_deriving_yojson, menhir, visitors, easy-format"
        exit 1
    }
    echo "F* built successfully!"
else
    echo "F* already built at $FSTAR_DIR/bin/fstar.exe"
fi

# Test F* installation
echo
echo "Testing F* installation..."
cd "$SCRIPT_DIR"
export FSTAR_HOME="$FSTAR_DIR"

# Create a simple test file
cat > test.fst << 'EOF'
module Test
let test_truth : squash (1 + 1 = 2) = ()
EOF

# Try to verify it
if "$FSTAR_HOME/bin/fstar.exe" test.fst > /dev/null 2>&1; then
    echo "✓ F* is working correctly!"
    rm -f test.fst test.fst.checked
else
    echo "✗ F* verification failed"
    rm -f test.fst
    exit 1
fi

echo
echo "=== Setup Complete ==="
echo
echo "You can now use F* for formal verification:"
echo "  cd $SCRIPT_DIR"
echo "  make verify    # Verify all proofs"
echo "  make extract   # Extract to C code"
echo "  make demo      # See what F* can prove"
echo
echo "Example proofs available:"
echo "  - T004: Soundness is exactly 122 bits"
echo "  - A001: Only SHA3 hashing allowed"
echo "  - A002: Zero-knowledge is mandatory"
echo "  - T201: No discrete log assumptions"
echo
echo "To integrate with truth buckets:"
echo "  1. Write formal specs in .fst files"
echo "  2. Prove properties mathematically"
echo "  3. Extract verified C code"
echo "  4. Link with truth verifier"