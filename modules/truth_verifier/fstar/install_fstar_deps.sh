#!/bin/bash
# Install F* dependencies on openSUSE

set -e

echo "=== Installing F* Dependencies on openSUSE ==="
echo

# Check if running on openSUSE
if ! grep -q "openSUSE" /etc/os-release; then
    echo "Warning: This script is designed for openSUSE"
fi

# Function to check if a command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Install Z3
if ! command_exists z3; then
    echo "Installing Z3..."
    sudo zypper install -y z3 || {
        echo "Failed to install z3 via zypper"
        echo "Alternative: Download Z3 binary from GitHub"
        echo "  wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip"
        echo "  unzip z3-4.13.0-x64-glibc-2.35.zip"
        echo "  sudo cp z3-4.13.0-x64-glibc-2.35/bin/z3 /usr/local/bin/"
    }
else
    echo "✓ Z3 already installed"
fi

# Install OCaml and OPAM if needed
if ! command_exists opam; then
    echo "Installing OCaml and OPAM..."
    sudo zypper install -y ocaml opam
else
    echo "✓ OPAM already installed"
fi

# Alternative: Download pre-built Z3
if ! command_exists z3; then
    echo
    echo "=== Alternative: Installing Z3 from binary ==="
    cd /tmp
    wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip
    unzip -o z3-4.13.0-x64-glibc-2.35.zip
    sudo mkdir -p /usr/local/bin
    sudo cp z3-4.13.0-x64-glibc-2.35/bin/z3 /usr/local/bin/
    sudo chmod +x /usr/local/bin/z3
    echo "✓ Z3 installed to /usr/local/bin/z3"
fi

# Test Z3
if command_exists z3; then
    echo
    echo "Testing Z3..."
    z3 --version
    echo "✓ Z3 is working!"
else
    echo "✗ Z3 installation failed"
    exit 1
fi

echo
echo "=== Installation Complete ==="
echo
echo "You can now run F* proofs with:"
echo "  cd modules/truth_verifier/fstar"
echo "  /home/bob/github/gate_computer/vendor/fstar_binary/bin/fstar.exe BaseFoldSecurity.fst"