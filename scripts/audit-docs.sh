#!/usr/bin/env bash
# ============================================================================
# audit-docs.sh — MANDATORY documentation audit before any commit
#
# This script scans the codebase and compares actual metrics against
# documented values. Any discrepancy MUST be resolved before commit.
#
# Usage:
#   bash scripts/audit-docs.sh           # Full audit with report
#   bash scripts/audit-docs.sh --quick   # Quick check, exit code only
#
# Exit codes:
#   0 — All documentation is current
#   1 — Discrepancies found (BLOCK COMMIT)
#   2 — Script error
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
QUICK_MODE="${1:-}"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

echo ""
echo "================================================================"
echo "  RIINA DOCUMENTATION AUDIT"
echo "================================================================"
echo ""

DISCREPANCIES=0
WARNINGS=0

# ── Helper functions ──────────────────────────────────────────────────

count_qed_active() {
    local total=0
    while IFS= read -r f; do
        local count=$(grep -c "Qed" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            total=$((total + count))
        fi
    done < <(find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f ! -path "*/_archive_deprecated/*" 2>/dev/null)
    echo "$total"
}

count_admitted_active() {
    find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f \
        ! -path "*/_archive_deprecated/*" \
        -exec grep -l "." {} \; 2>/dev/null | \
        xargs grep -c "Admitted\." 2>/dev/null | \
        awk -F: '{sum += $2} END {print sum+0}'
}

count_coq_files() {
    find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f 2>/dev/null | wc -l
}

count_rust_tests() {
    cd "$REPO_ROOT/03_PROTO" && cargo test --no-run 2>&1 | \
        grep -oP '\d+ tests' | head -1 | grep -oP '^\d+' || echo "0"
}

count_examples() {
    find "$REPO_ROOT/07_EXAMPLES" -name "*.rii" -type f 2>/dev/null | wc -l
}

get_session_from_log() {
    grep -oP "Session \K\d+" "$REPO_ROOT/SESSION_LOG.md" 2>/dev/null | head -1 || echo "0"
}

check_value() {
    local name="$1"
    local actual="$2"
    local documented="$3"
    local file="$4"

    if [ "$actual" != "$documented" ]; then
        echo -e "${RED}[MISMATCH]${NC} $name"
        echo "           Actual:     $actual"
        echo "           Documented: $documented (in $file)"
        ((DISCREPANCIES++))
        return 1
    else
        echo -e "${GREEN}[OK]${NC} $name: $actual"
        return 0
    fi
}

warn_check() {
    local name="$1"
    local status="$2"

    if [ "$status" = "missing" ]; then
        echo -e "${YELLOW}[WARN]${NC} $name"
        ((WARNINGS++))
    fi
}

# ── Gather actual metrics ─────────────────────────────────────────────

echo -e "${CYAN}Scanning codebase...${NC}"
echo ""

ACTUAL_QED=$(count_qed_active)
ACTUAL_ADMITTED=$(count_admitted_active)
ACTUAL_COQ_FILES=$(count_coq_files)
ACTUAL_EXAMPLES=$(count_examples)
ACTUAL_SESSION=$(get_session_from_log)

echo "Actual metrics from codebase:"
echo "  Qed (active):  $ACTUAL_QED"
echo "  Admitted:      $ACTUAL_ADMITTED"
echo "  Coq files:     $ACTUAL_COQ_FILES"
echo "  Examples:      $ACTUAL_EXAMPLES"
echo "  Session:       $ACTUAL_SESSION"
echo ""

# ── Check CLAUDE.md ───────────────────────────────────────────────────

echo -e "${CYAN}Checking CLAUDE.md...${NC}"

if [ -f "$REPO_ROOT/CLAUDE.md" ]; then
    # Extract documented values from CLAUDE.md
    DOC_QED=$(grep -oP '\d+,?\d* Qed' "$REPO_ROOT/CLAUDE.md" | head -1 | grep -oP '^\d+,?\d*' | tr -d ',' || echo "0")
    DOC_SESSION=$(grep -oP 'Session \K\d+' "$REPO_ROOT/CLAUDE.md" | head -1 || echo "0")

    check_value "Qed proofs (CLAUDE.md)" "$ACTUAL_QED" "$DOC_QED" "CLAUDE.md" || true
    check_value "Session number (CLAUDE.md)" "$ACTUAL_SESSION" "$DOC_SESSION" "CLAUDE.md" || true
else
    echo -e "${RED}[ERROR]${NC} CLAUDE.md not found!"
    ((DISCREPANCIES++))
fi
echo ""

# ── Check README.md ───────────────────────────────────────────────────

echo -e "${CYAN}Checking README.md...${NC}"

if [ -f "$REPO_ROOT/README.md" ]; then
    DOC_README_QED=$(grep -oP '\d+,?\d*\+? theorems' "$REPO_ROOT/README.md" | head -1 | grep -oP '^\d+,?\d*' | tr -d ',' || echo "0")

    if [ -n "$DOC_README_QED" ] && [ "$DOC_README_QED" != "0" ]; then
        # Allow some tolerance for README (it may say "6,700+" instead of exact)
        if [ "$ACTUAL_QED" -ge "$DOC_README_QED" ]; then
            echo -e "${GREEN}[OK]${NC} README theorem count: $DOC_README_QED (actual: $ACTUAL_QED)"
        else
            echo -e "${YELLOW}[WARN]${NC} README may need update: documented $DOC_README_QED, actual $ACTUAL_QED"
            ((WARNINGS++))
        fi
    fi
else
    echo -e "${YELLOW}[WARN]${NC} README.md not found"
    ((WARNINGS++))
fi
echo ""

# ── Check website metrics.json ────────────────────────────────────────

echo -e "${CYAN}Checking website/public/metrics.json...${NC}"

METRICS_FILE="$REPO_ROOT/website/public/metrics.json"
if [ -f "$METRICS_FILE" ]; then
    WEB_QED=$(grep -oP '"qedActive":\s*\K\d+' "$METRICS_FILE" || echo "0")
    WEB_SESSION=$(grep -oP '"session":\s*\K\d+' "$METRICS_FILE" || echo "0")

    check_value "Website Qed (metrics.json)" "$ACTUAL_QED" "$WEB_QED" "metrics.json" || true
    check_value "Website Session (metrics.json)" "$ACTUAL_SESSION" "$WEB_SESSION" "metrics.json" || true
else
    echo -e "${YELLOW}[WARN]${NC} metrics.json not found (run: bash scripts/generate-metrics.sh)"
    ((WARNINGS++))
fi
echo ""

# ── Check RiinaWebsite.jsx hero stats ─────────────────────────────────

echo -e "${CYAN}Checking website hero stats...${NC}"

WEBSITE_JSX="$REPO_ROOT/website/src/RiinaWebsite.jsx"
if [ -f "$WEBSITE_JSX" ]; then
    HERO_QED=$(grep -oP "value:\s*'\K[\d,]+" "$WEBSITE_JSX" | head -1 | tr -d ',' || echo "0")

    if [ -n "$HERO_QED" ] && [ "$HERO_QED" != "0" ]; then
        check_value "Website hero Qed" "$ACTUAL_QED" "$HERO_QED" "RiinaWebsite.jsx" || true
    fi
else
    echo -e "${YELLOW}[WARN]${NC} RiinaWebsite.jsx not found"
    ((WARNINGS++))
fi
echo ""

# ── Check hooks are installed ─────────────────────────────────────────

echo -e "${CYAN}Checking git hooks...${NC}"

if [ -f "$REPO_ROOT/.git/hooks/pre-commit" ]; then
    if grep -q "riinac verify" "$REPO_ROOT/.git/hooks/pre-commit" 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} pre-commit hook installed (riinac verify)"
    else
        echo -e "${RED}[ERROR]${NC} pre-commit hook exists but is NOT the RIINA hook!"
        echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
        ((DISCREPANCIES++))
    fi
else
    echo -e "${RED}[ERROR]${NC} pre-commit hook NOT installed!"
    echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
    ((DISCREPANCIES++))
fi

if [ -f "$REPO_ROOT/.git/hooks/pre-push" ]; then
    if grep -q "riinac verify" "$REPO_ROOT/.git/hooks/pre-push" 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} pre-push hook installed (riinac verify --full)"
    else
        echo -e "${RED}[ERROR]${NC} pre-push hook exists but is NOT the RIINA hook!"
        echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
        ((DISCREPANCIES++))
    fi
else
    echo -e "${RED}[ERROR]${NC} pre-push hook NOT installed!"
    echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
    ((DISCREPANCIES++))
fi
echo ""

# ── Final report ──────────────────────────────────────────────────────

echo "================================================================"
if [ "$DISCREPANCIES" -gt 0 ]; then
    echo -e "  ${RED}AUDIT FAILED${NC}"
    echo ""
    echo "  Discrepancies: $DISCREPANCIES"
    echo "  Warnings:      $WARNINGS"
    echo ""
    echo "  FIX ALL DISCREPANCIES BEFORE COMMITTING."
    echo "  Update documentation to match actual metrics."
    echo "================================================================"
    exit 1
elif [ "$WARNINGS" -gt 0 ]; then
    echo -e "  ${YELLOW}AUDIT PASSED WITH WARNINGS${NC}"
    echo ""
    echo "  Discrepancies: 0"
    echo "  Warnings:      $WARNINGS"
    echo ""
    echo "  Review warnings. Proceed with caution."
    echo "================================================================"
    exit 0
else
    echo -e "  ${GREEN}AUDIT PASSED${NC}"
    echo ""
    echo "  All documentation is current."
    echo "  Proceed with commit."
    echo "================================================================"
    exit 0
fi
