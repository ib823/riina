#!/usr/bin/env bash
# RIINA Installer — builds from source and installs riinac
# Usage: curl -sSf https://raw.githubusercontent.com/ib823/riina/main/scripts/install.sh | bash
# Or:    bash scripts/install.sh

set -euo pipefail

INSTALL_DIR="${RIINA_HOME:-$HOME/.riina}/bin"

echo "=== RIINA Installer ==="
echo ""

# Check Rust toolchain
if ! command -v cargo &>/dev/null; then
    echo "ERROR: Rust toolchain not found."
    echo "Install Rust first: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    exit 1
fi

RUST_VERSION=$(rustc --version | awk '{print $2}')
echo "Rust version: $RUST_VERSION"

# Determine source directory
if [ -f "03_PROTO/Cargo.toml" ]; then
    PROTO_DIR="03_PROTO"
elif [ -f "Cargo.toml" ] && grep -q 'riinac' Cargo.toml; then
    PROTO_DIR="."
else
    echo "ERROR: Cannot find RIINA source."
    echo "Run this script from the repository root, or clone first:"
    echo "  git clone https://github.com/ib823/riina.git && cd riina"
    exit 1
fi

# Build
echo "Building riinac (release)..."
cargo build --release --manifest-path "$PROTO_DIR/Cargo.toml"

BINARY="$PROTO_DIR/target/release/riinac"
if [ ! -f "$BINARY" ]; then
    echo "ERROR: Build failed — binary not found."
    exit 1
fi

# Install
echo "Installing to $INSTALL_DIR..."
mkdir -p "$INSTALL_DIR"
cp "$BINARY" "$INSTALL_DIR/riinac"
chmod +x "$INSTALL_DIR/riinac"

# PATH hint
if [[ ":$PATH:" != *":$INSTALL_DIR:"* ]]; then
    echo ""
    echo "Add riinac to your PATH:"
    echo "  export PATH=\"$INSTALL_DIR:\$PATH\""
    echo ""
    echo "Or add to your shell profile (~/.bashrc, ~/.zshrc):"
    echo "  echo 'export PATH=\"$INSTALL_DIR:\$PATH\"' >> ~/.bashrc"
fi

echo ""
echo "=== Installation Complete ==="
echo "Run: $INSTALL_DIR/riinac --help"
