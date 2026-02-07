#!/usr/bin/env bash
# ============================================================================
# verify-public.sh — Post-sync verification for public branch
#
# Runs AFTER sync-public.sh commits on public, BEFORE push.
# Ensures no internal files, private references, or contamination.
#
# Usage: bash scripts/verify-public.sh
# Exit codes:
#   0 — Public branch is clean
#   1 — Contamination detected (DO NOT PUSH)
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
FAIL=0

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

echo ""
echo "================================================================"
echo "  RIINA PUBLIC BRANCH VERIFICATION"
echo "================================================================"
echo ""

# ── 1. No private repo URL references ────────────────────────────────
echo "[1/8] Checking for ib823/proof references..."
if grep -ri 'ib823/proof' "$REPO_ROOT" \
    --include='*.md' --include='*.toml' --include='*.json' \
    --include='*.nix' --include='*.sh' --include='*.txt' \
    2>/dev/null | grep -v '\.git/' | grep -v 'verify-public.sh'; then
    echo -e "${RED}FAIL: ib823/proof reference found${NC}"
    FAIL=1
else
    echo -e "${GREEN}[OK] No ib823/proof references${NC}"
fi

# ── 2. No internal files ─────────────────────────────────────────────
echo "[2/8] Checking for internal files..."
for f in CLAUDE.md PROGRESS.md SESSION_LOG.md VERIFICATION_MANIFEST.md \
         REPO_PROTECTION_GUIDE.md axiom_audit_report.txt; do
    if [ -f "$REPO_ROOT/$f" ]; then
        echo -e "${RED}FAIL: $f exists on public branch${NC}"
        FAIL=1
    fi
done

# ── 3. No internal directories ───────────────────────────────────────
echo "[3/8] Checking for internal directories..."
for d in 01_RESEARCH 06_COORDINATION 99_ARCHIVE claude_ai_output dist 04_SPECS/business; do
    if [ -d "$REPO_ROOT/$d" ]; then
        echo -e "${RED}FAIL: $d/ exists on public branch${NC}"
        FAIL=1
    fi
done

# ── 4. No Co-Authored-By in scripts ──────────────────────────────────
echo "[4/8] Checking for Co-Authored-By in scripts..."
if grep -ri 'Co-Authored-By.*anthropic' "$REPO_ROOT/scripts/" 2>/dev/null | grep -v 'verify-public.sh'; then
    echo -e "${RED}FAIL: Co-Authored-By in scripts${NC}"
    FAIL=1
else
    echo -e "${GREEN}[OK] No Co-Authored-By in scripts${NC}"
fi

# ── 5. License consistency ────────────────────────────────────────────
echo "[5/8] Checking license consistency..."
LICENSE_FAIL=0
for f in riina-vscode/package.json website/package.json; do
    if [ -f "$REPO_ROOT/$f" ] && ! grep -q '"Proprietary"' "$REPO_ROOT/$f"; then
        echo -e "${RED}FAIL: $f license is not Proprietary${NC}"
        FAIL=1
        LICENSE_FAIL=1
    fi
done
for f in 03_PROTO/Cargo.toml 05_TOOLING/Cargo.toml; do
    if [ -f "$REPO_ROOT/$f" ] && ! grep -q 'license = "Proprietary"' "$REPO_ROOT/$f"; then
        echo -e "${RED}FAIL: $f license is not Proprietary${NC}"
        FAIL=1
        LICENSE_FAIL=1
    fi
done
if [ $LICENSE_FAIL -eq 0 ]; then
    echo -e "${GREEN}[OK] All licenses Proprietary${NC}"
fi

# ── 6. Governance files exist ─────────────────────────────────────────
echo "[6/8] Checking governance files..."
GOV_FAIL=0
for f in SECURITY.md CODE_OF_CONDUCT.md CONTRIBUTING.md LICENSE; do
    if [ ! -f "$REPO_ROOT/$f" ]; then
        echo -e "${RED}FAIL: $f missing${NC}"
        FAIL=1
        GOV_FAIL=1
    fi
done
if [ $GOV_FAIL -eq 0 ]; then
    echo -e "${GREEN}[OK] All governance files present${NC}"
fi

# ── 7. No /workspaces/proof hardcoded paths ───────────────────────────
echo "[7/8] Checking for /workspaces/proof paths..."
if grep -r '/workspaces/proof' "$REPO_ROOT" \
    --include='*.sh' --include='*.md' --include='*.toml' \
    --include='*.json' --include='*.nix' --include='*.txt' \
    2>/dev/null | grep -v '\.git/' | grep -v 'verify-public.sh'; then
    echo -e "${RED}FAIL: /workspaces/proof hardcoded path found${NC}"
    FAIL=1
else
    echo -e "${GREEN}[OK] No /workspaces/proof paths${NC}"
fi

# ── 8. No backup/strategy files ──────────────────────────────────────
echo "[8/8] Checking for stray internal documents..."
STRAY=$(find "$REPO_ROOT" -type f \( \
    -name "*.bak" -o -name "*.backup" -o \
    -name "CLAUDE_*.md" -o -name "DELEGATION_TASKS.md" -o \
    -name "TASK_PROMPTS.md" -o -name "*STRATEGY*.md" -o \
    -name "*ATTACK*.md" -o -name "*GAP_CLOSURE*.md" -o \
    -name "*PRIME_DIRECTIVE*.md" \
    \) ! -path '*/.git/*' 2>/dev/null || true)
if [ -n "$STRAY" ]; then
    echo -e "${RED}FAIL: Stray internal documents found:${NC}"
    echo "$STRAY"
    FAIL=1
else
    echo -e "${GREEN}[OK] No stray internal documents${NC}"
fi

# ── Result ────────────────────────────────────────────────────────────
echo ""
echo "================================================================"
if [ $FAIL -eq 0 ]; then
    echo -e "  ${GREEN}PUBLIC BRANCH VERIFIED — SAFE TO PUSH${NC}"
    echo "================================================================"
    exit 0
else
    echo -e "  ${RED}PUBLIC BRANCH CONTAMINATED — DO NOT PUSH${NC}"
    echo "================================================================"
    exit 1
fi
