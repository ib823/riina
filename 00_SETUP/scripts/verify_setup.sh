#!/bin/bash
# TERAS Setup Verification Script

set -euo pipefail

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║              TERAS Setup Verification                        ║"
echo "╚══════════════════════════════════════════════════════════════╝"

ERRORS=0

# Check Rust
echo ""
echo "Checking Rust..."
if command -v rustc &> /dev/null; then
    echo "  ✅ rustc: $(rustc --version)"
    echo "  ✅ cargo: $(cargo --version)"
else
    echo "  ❌ Rust not found"
    ERRORS=$((ERRORS + 1))
fi

# Check Coq
echo ""
echo "Checking Coq..."
if command -v coqc &> /dev/null; then
    echo "  ✅ coqc: $(coqc --version | head -1)"
else
    echo "  ❌ Coq not found"
    ERRORS=$((ERRORS + 1))
fi

# Check Lean (optional)
echo ""
echo "Checking Lean..."
if command -v lean &> /dev/null; then
    echo "  ✅ lean: $(lean --version)"
else
    echo "  ⚠️  Lean not found (optional)"
fi

# Check directory structure
echo ""
echo "Checking directory structure..."
DIRS=(
    "/workspaces/proof/01_RESEARCH"
    "/workspaces/proof/02_FORMAL/coq"
    "/workspaces/proof/03_PROTO"
    "/workspaces/proof/05_TOOLING"
    "/workspaces/proof/06_COORDINATION"
)

for dir in "${DIRS[@]}"; do
    if [ -d "$dir" ]; then
        echo "  ✅ $dir"
    else
        echo "  ❌ $dir missing"
        ERRORS=$((ERRORS + 1))
    fi
done

# Check key files
echo ""
echo "Checking key files..."
FILES=(
    "/workspaces/proof/CONTRIBUTING.md"
    "/workspaces/proof/02_FORMAL/coq/_CoqProject"
    "/workspaces/proof/05_TOOLING/Cargo.toml"
)

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "  ✅ $file"
    else
        echo "  ❌ $file missing"
        ERRORS=$((ERRORS + 1))
    fi
done

# Summary
echo ""
echo "════════════════════════════════════════════════════════════════"
if [ $ERRORS -eq 0 ]; then
    echo "✅ All checks passed!"
    echo ""
    echo "You can now proceed with development."
    exit 0
else
    echo "❌ $ERRORS checks failed"
    echo ""
    echo "Please fix the issues above before proceeding."
    exit 1
fi
