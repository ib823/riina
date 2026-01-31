#!/bin/bash
# RIINA Rocq Installation Script
# Installs Rocq 9.1 (Coq 8.21) for formal proofs

set -euo pipefail

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║              RIINA Rocq Installation Script                  ║"
echo "╚══════════════════════════════════════════════════════════════╝"

# Check if already installed
if command -v coqc &> /dev/null; then
    VERSION=$(coqc --version | head -1)
    echo "Rocq/Coq already installed: $VERSION"
    exit 0
fi

echo "Installing Rocq 9.1 (Coq 8.21)..."

# Install via opam (preferred method)
if command -v opam &> /dev/null; then
    opam update
    opam install coq.8.21.0 -y
    eval $(opam env)
else
    # Install opam first
    echo "Installing opam..."
    sudo apt-get update
    sudo apt-get install -y opam
    opam init --auto-setup --yes --disable-sandboxing
    eval $(opam env)
    opam update
    opam install coq.8.21.0 -y
fi

# Verify installation
echo ""
echo "Verifying installation..."
coqc --version

echo ""
echo "✅ Rocq 9.1 (Coq 8.21) installation complete"
