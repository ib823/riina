#!/usr/bin/env bash
# Copyright (c) 2026 The RIINA Authors. All rights reserved.
# Build RIINA WASM binary for the playground.
#
# Usage: bash scripts/build-wasm.sh
#
# Prerequisites:
#   rustup target add wasm32-unknown-unknown
#
# Output:
#   website/public/riina_wasm.wasm

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Ensure Rust toolchain is on PATH
if [ -d "$HOME/.cargo/bin" ]; then
    export PATH="$HOME/.cargo/bin:$PATH"
fi

echo "=== RIINA WASM Build ==="
echo "Root: $ROOT_DIR"

# Check wasm32 target
if ! rustup target list --installed 2>/dev/null | grep -q wasm32-unknown-unknown; then
    echo "Adding wasm32-unknown-unknown target..."
    rustup target add wasm32-unknown-unknown
fi

# Build riina-wasm crate for wasm32
echo "Building riina-wasm for wasm32-unknown-unknown..."
cd "$ROOT_DIR/03_PROTO"
cargo build --target wasm32-unknown-unknown --release -p riina-wasm 2>&1 || {
    echo "WARNING: WASM build failed (platform deps may need feature-gating)."
    echo "The playground will use a stub .wasm file."
    # Create a minimal valid WASM module as stub
    mkdir -p "$ROOT_DIR/website/public"
    printf '\x00asm\x01\x00\x00\x00' > "$ROOT_DIR/website/public/riina_wasm.wasm"
    echo "Stub .wasm created at website/public/riina_wasm.wasm"
    exit 0
}

# Copy to website
WASM_FILE="$ROOT_DIR/03_PROTO/target/wasm32-unknown-unknown/release/riina_wasm.wasm"
if [ -f "$WASM_FILE" ]; then
    mkdir -p "$ROOT_DIR/website/public"
    cp "$WASM_FILE" "$ROOT_DIR/website/public/riina_wasm.wasm"
    echo "Copied .wasm to website/public/riina_wasm.wasm"
    ls -lh "$ROOT_DIR/website/public/riina_wasm.wasm"
else
    echo "WARNING: .wasm file not found at $WASM_FILE"
    mkdir -p "$ROOT_DIR/website/public"
    printf '\x00asm\x01\x00\x00\x00' > "$ROOT_DIR/website/public/riina_wasm.wasm"
    echo "Stub .wasm created."
fi

echo "=== WASM build complete ==="
