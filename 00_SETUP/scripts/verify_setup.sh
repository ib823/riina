#!/bin/bash
# RIINA Setup Verification Script

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

echo "========================================================"
echo "  RIINA Setup Verification"
echo "========================================================"

ERRORS=0

# Check Rust
echo ""
echo "Checking Rust..."
if command -v rustc &> /dev/null; then
    echo "  [OK] rustc: $(rustc --version)"
    echo "  [OK] cargo: $(cargo --version)"
else
    echo "  [FAIL] Rust not found"
    ERRORS=$((ERRORS + 1))
fi

# Check Coq
echo ""
echo "Checking Coq..."
if command -v coqc &> /dev/null; then
    echo "  [OK] coqc: $(coqc --version | head -1)"
else
    echo "  [FAIL] Coq not found"
    ERRORS=$((ERRORS + 1))
fi

# Check Lean (optional)
echo ""
echo "Checking Lean..."
if command -v lean &> /dev/null; then
    echo "  [OK] lean: $(lean --version)"
else
    echo "  [INFO] Lean not found (optional)"
fi

# Check directory structure
echo ""
echo "Checking directory structure..."
DIRS=(
    "$REPO_ROOT/02_FORMAL/coq"
    "$REPO_ROOT/03_PROTO"
    "$REPO_ROOT/05_TOOLING"
)

for dir in "${DIRS[@]}"; do
    if [ -d "$dir" ]; then
        echo "  [OK] $dir"
    else
        echo "  [FAIL] $dir missing"
        ERRORS=$((ERRORS + 1))
    fi
done

# Check key files
echo ""
echo "Checking key files..."
FILES=(
    "$REPO_ROOT/02_FORMAL/coq/_CoqProject"
    "$REPO_ROOT/05_TOOLING/Cargo.toml"
)

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "  [OK] $file"
    else
        echo "  [FAIL] $file missing"
        ERRORS=$((ERRORS + 1))
    fi
done

# Summary
echo ""
echo "========================================================"
if [ $ERRORS -eq 0 ]; then
    echo "[OK] All checks passed!"
    echo ""
    echo "You can now proceed with development."
    exit 0
else
    echo "[FAIL] $ERRORS checks failed"
    echo ""
    echo "Please fix the issues above before proceeding."
    exit 1
fi
