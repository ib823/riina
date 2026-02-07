#!/bin/bash
# RIINA Rust Installation Script

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

echo "========================================================"
echo "  RIINA Rust Installation Script"
echo "========================================================"

# Check if already installed
if command -v rustc &> /dev/null; then
    VERSION=$(rustc --version)
    echo "Rust already installed: $VERSION"

    # Check if correct version
    if [[ "$VERSION" == *"1.84"* ]] || [[ "$VERSION" == *"1.85"* ]] || [[ "$VERSION" == *"1.86"* ]]; then
        echo "Version is compatible"
        exit 0
    fi
fi

echo "Installing Rust..."

# Install rustup
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Add to PATH
source "$HOME/.cargo/env"

# Install specific version (from rust-toolchain.toml)
if [ -f "$REPO_ROOT/05_TOOLING/rust-toolchain.toml" ]; then
    cd "$REPO_ROOT/05_TOOLING"
    rustup show
else
    rustup default stable
fi

# Install additional components
rustup component add clippy rustfmt

# Verify installation
echo ""
echo "Verifying installation..."
rustc --version
cargo --version
clippy-driver --version

echo ""
echo "[OK] Rust installation complete"
