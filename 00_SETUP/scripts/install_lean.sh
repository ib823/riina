#!/bin/bash
# TERAS Lean 4 Installation Script

set -euo pipefail

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║              TERAS Lean 4 Installation Script                ║"
echo "╚══════════════════════════════════════════════════════════════╝"

# Check if already installed
if command -v lean &> /dev/null; then
    VERSION=$(lean --version)
    echo "Lean already installed: $VERSION"
    exit 0
fi

echo "Installing Lean 4 via elan..."

# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add to PATH
export PATH="$HOME/.elan/bin:$PATH"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Install latest stable Lean 4
elan default leanprover/lean4:stable

# Verify installation
echo ""
echo "Verifying installation..."
lean --version

echo ""
echo "✅ Lean 4 installation complete"
