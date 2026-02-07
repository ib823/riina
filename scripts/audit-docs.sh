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

if [ "$QUICK_MODE" != "--quick" ]; then
    echo ""
    echo "================================================================"
    echo "  RIINA DOCUMENTATION AUDIT"
    echo "================================================================"
    echo ""
fi

DISCREPANCIES=0
WARNINGS=0

# ── Helper functions ──────────────────────────────────────────────────

count_qed_active() {
    local total=0
    while IFS= read -r f; do
        local count=$(grep -c "Qed\." "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            total=$((total + count))
        fi
    done < <(find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f ! -path "*/_archive_deprecated/*" 2>/dev/null)
    echo "$total"
}

count_admitted_active() {
    local total=0
    while IFS= read -r f; do
        local count=$(grep -cP '^\s*Admitted\.' "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            total=$((total + count))
        fi
    done < <(find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f ! -path "*/_archive_deprecated/*" 2>/dev/null)
    echo "$total"
}

count_coq_files() {
    find "$REPO_ROOT/02_FORMAL/coq" -name "*.v" -type f 2>/dev/null | wc -l
}

count_lean_theorems() {
    local total=0
    while IFS= read -r f; do
        local count=$(grep -cP "^\s*(theorem|lemma)\s" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            total=$((total + count))
        fi
    done < <(find "$REPO_ROOT/02_FORMAL/lean" -name "*.lean" -type f ! -name "lakefile.lean" 2>/dev/null)
    echo "$total"
}

count_isabelle_lemmas() {
    local total=0
    while IFS= read -r f; do
        local count=$(grep -cP "^\s*(lemma|theorem|corollary)\s" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            total=$((total + count))
        fi
    done < <(find "$REPO_ROOT/02_FORMAL/isabelle" -name "*.thy" -type f 2>/dev/null)
    echo "$total"
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
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${RED}[MISMATCH]${NC} $name"
            echo "           Actual:     $actual"
            echo "           Documented: $documented (in $file)"
        fi
        DISCREPANCIES=$((DISCREPANCIES + 1))
        return 1
    else
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${GREEN}[OK]${NC} $name: $actual"
        fi
        return 0
    fi
}

check_no_stale() {
    local file="$1"
    local pattern="$2"
    local desc="$3"

    if [ ! -f "$file" ]; then
        return 0
    fi

    if grep -qP "$pattern" "$file" 2>/dev/null; then
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${RED}[STALE]${NC} $desc in $(basename "$file")"
            echo "           Pattern found: $pattern"
        fi
        DISCREPANCIES=$((DISCREPANCIES + 1))
        return 1
    fi
    return 0
}

warn_check() {
    local name="$1"
    local status="$2"

    if [ "$status" = "missing" ]; then
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${YELLOW}[WARN]${NC} $name"
        fi
        WARNINGS=$((WARNINGS + 1))
    fi
}

# ── Gather actual metrics ─────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Scanning codebase...${NC}"
    echo ""
fi

ACTUAL_QED=$(count_qed_active)
ACTUAL_ADMITTED=$(count_admitted_active)
ACTUAL_COQ_FILES=$(count_coq_files)
ACTUAL_LEAN=$(count_lean_theorems)
ACTUAL_ISABELLE=$(count_isabelle_lemmas)
ACTUAL_TOTAL=$((ACTUAL_QED + ACTUAL_LEAN + ACTUAL_ISABELLE))
ACTUAL_EXAMPLES=$(count_examples)
ACTUAL_SESSION=$(get_session_from_log)
# Locale-independent thousands separator
add_commas() { echo "$1" | sed ':a;s/\B[0-9]\{3\}\>$/,&/;ta'; }
ACTUAL_QED_COMMA=$(add_commas "$ACTUAL_QED")

if [ "$QUICK_MODE" != "--quick" ]; then
    echo "Actual metrics from codebase:"
    echo "  Qed (active):  $ACTUAL_QED"
    echo "  Admitted:      $ACTUAL_ADMITTED"
    echo "  Coq files:     $ACTUAL_COQ_FILES"
    echo "  Lean:          $ACTUAL_LEAN theorems"
    echo "  Isabelle:      $ACTUAL_ISABELLE lemmas"
    echo "  Total proofs:  $ACTUAL_TOTAL"
    echo "  Examples:      $ACTUAL_EXAMPLES"
    echo "  Session:       $ACTUAL_SESSION"
    echo ""
fi

# ── Check CLAUDE.md ───────────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking CLAUDE.md...${NC}"
fi

if [ -f "$REPO_ROOT/CLAUDE.md" ]; then
    DOC_QED=$(grep -oP '\d+,?\d* Qed' "$REPO_ROOT/CLAUDE.md" | head -1 | grep -oP '^\d+,?\d*' | tr -d ',' || echo "0")
    DOC_SESSION=$(grep -oP 'Session \K\d+' "$REPO_ROOT/CLAUDE.md" | head -1 || echo "0")
    DOC_LEAN=$(grep -oP 'Lean 4 Theorems[*]{2} \| \K\d+' "$REPO_ROOT/CLAUDE.md" | head -1 || echo "0")
    DOC_ISABELLE=$(grep -oP 'Isabelle/HOL Lemmas[*]{2} \| \K\d+' "$REPO_ROOT/CLAUDE.md" | head -1 || echo "0")

    check_value "Qed proofs (CLAUDE.md)" "$ACTUAL_QED" "$DOC_QED" "CLAUDE.md" || true
    check_value "Lean theorems (CLAUDE.md)" "$ACTUAL_LEAN" "$DOC_LEAN" "CLAUDE.md" || true
    check_value "Isabelle lemmas (CLAUDE.md)" "$ACTUAL_ISABELLE" "$DOC_ISABELLE" "CLAUDE.md" || true
    # Session number is internal tracking — warn but don't block
    if [ "$ACTUAL_SESSION" != "$DOC_SESSION" ]; then
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${YELLOW}[WARN]${NC} Session number (CLAUDE.md): actual=$ACTUAL_SESSION, documented=$DOC_SESSION"
        fi
        WARNINGS=$((WARNINGS + 1))
    else
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${GREEN}[OK]${NC} Session number (CLAUDE.md): $DOC_SESSION"
        fi
    fi
else
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "${RED}[ERROR]${NC} CLAUDE.md not found!"
    fi
    DISCREPANCIES=$((DISCREPANCIES + 1))
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check README.md ───────────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking README.md...${NC}"
fi

if [ -f "$REPO_ROOT/README.md" ]; then
    # Check for known-stale Qed counts (historical values that should never appear)
    check_no_stale "$REPO_ROOT/README.md" "6,193|6193" "Stale Qed count (6,193)" || true
    check_no_stale "$REPO_ROOT/README.md" "4,044|4044" "Stale Qed count (4,044)" || true

    # Dynamically check that README Lean/Isabelle/Qed match actual counts
    README_QED=$(grep -oP '[0-9,]+ Coq Qed' "$REPO_ROOT/README.md" | head -1 | grep -oP '^[0-9,]+' | tr -d ',' || echo "0")
    if [ "$README_QED" != "0" ] && [ "$README_QED" != "$ACTUAL_QED" ]; then
        check_value "Qed in README.md" "$ACTUAL_QED" "$README_QED" "README.md" || true
    fi
else
    warn_check "README.md not found" "missing"
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check SECURITY.md ────────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking SECURITY.md...${NC}"
fi

if [ -f "$REPO_ROOT/SECURITY.md" ]; then
    check_no_stale "$REPO_ROOT/SECURITY.md" "6,193" "Stale Qed count (6,193)" || true
    check_no_stale "$REPO_ROOT/SECURITY.md" "4,044" "Stale Qed count (4,044)" || true
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check CONTRIBUTING.md ────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking CONTRIBUTING.md...${NC}"
fi

if [ -f "$REPO_ROOT/CONTRIBUTING.md" ]; then
    check_no_stale "$REPO_ROOT/CONTRIBUTING.md" "6,193|6193" "Stale Qed count (6,193)" || true
    check_no_stale "$REPO_ROOT/CONTRIBUTING.md" "Rocq 9\\.1" "Stale prover ref (Rocq 9.1)" || true
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check CHANGELOG.md ───────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking CHANGELOG.md banner...${NC}"
fi

if [ -f "$REPO_ROOT/CHANGELOG.md" ]; then
    CL_QED=$(grep -oP '\d+,?\d* Coq Qed' "$REPO_ROOT/CHANGELOG.md" | head -1 | grep -oP '^\d+,?\d*' | tr -d ',' || echo "0")
    check_value "Qed in CHANGELOG.md banner" "$ACTUAL_QED" "$CL_QED" "CHANGELOG.md" || true
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check PROGRESS.md ────────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking PROGRESS.md...${NC}"
fi

if [ -f "$REPO_ROOT/PROGRESS.md" ]; then
    PG_QED=$(grep -oP 'Qed Proofs \(Coq\) \| \*\*\K[0-9,]+' "$REPO_ROOT/PROGRESS.md" | tr -d ',' || echo "0")
    check_value "Qed in PROGRESS.md table" "$ACTUAL_QED" "$PG_QED" "PROGRESS.md" || true
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check website metrics.json ────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking website/public/metrics.json...${NC}"
fi

METRICS_FILE="$REPO_ROOT/website/public/metrics.json"
if [ -f "$METRICS_FILE" ]; then
    WEB_QED=$(grep -oP '"qedActive":\s*\K\d+' "$METRICS_FILE" || echo "0")
    WEB_SESSION=$(grep -oP '"session":\s*\K\d+' "$METRICS_FILE" || echo "0")
    WEB_LEAN=$(python3 -c "import json; print(json.load(open('$METRICS_FILE'))['lean']['theorems'])" 2>/dev/null || grep -oP '"theorems":\s*\K\d+' "$METRICS_FILE" | head -1 || echo "0")
    WEB_ISABELLE=$(python3 -c "import json; print(json.load(open('$METRICS_FILE'))['isabelle']['lemmas'])" 2>/dev/null || grep -oP '"lemmas":\s*\K\d+' "$METRICS_FILE" | head -1 || echo "0")

    check_value "Website Qed (metrics.json)" "$ACTUAL_QED" "$WEB_QED" "metrics.json" || true
    check_value "Website Lean (metrics.json)" "$ACTUAL_LEAN" "$WEB_LEAN" "metrics.json" || true
    check_value "Website Isabelle (metrics.json)" "$ACTUAL_ISABELLE" "$WEB_ISABELLE" "metrics.json" || true
    # Session number is internal tracking — warn but don't block
    if [ "$ACTUAL_SESSION" != "$WEB_SESSION" ]; then
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${YELLOW}[WARN]${NC} Website Session (metrics.json): actual=$ACTUAL_SESSION, documented=$WEB_SESSION"
        fi
        WARNINGS=$((WARNINGS + 1))
    else
        if [ "$QUICK_MODE" != "--quick" ]; then
            echo -e "${GREEN}[OK]${NC} Website Session (metrics.json): $WEB_SESSION"
        fi
    fi
else
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "${YELLOW}[WARN]${NC} metrics.json not found (run: bash scripts/generate-metrics.sh)"
    fi
    WARNINGS=$((WARNINGS + 1))
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check RiinaWebsite.jsx hero stats ─────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking website hero stats...${NC}"
fi

WEBSITE_JSX="$REPO_ROOT/website/src/RiinaWebsite.jsx"
if [ -f "$WEBSITE_JSX" ]; then
    # Check for known-stale counts in JSX (historical values that should never appear)
    check_no_stale "$WEBSITE_JSX" "7,875|7875" "Stale total (7,875)" || true
else
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "${YELLOW}[WARN]${NC} RiinaWebsite.jsx not found"
    fi
    WARNINGS=$((WARNINGS + 1))
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check website/index.html ─────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking website/index.html...${NC}"
fi

INDEX_HTML="$REPO_ROOT/website/index.html"
if [ -f "$INDEX_HTML" ]; then
    check_no_stale "$INDEX_HTML" "7,875|7875" "Stale total proofs (7,875)" || true
fi
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check enterprise docs for Rocq 9.1 ───────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking enterprise docs...${NC}"
fi

for ent_file in "$REPO_ROOT/docs/enterprise/CERTIFICATION.md" "$REPO_ROOT/docs/enterprise/COMPLIANCE_PACKAGING.md"; do
    if [ -f "$ent_file" ]; then
        check_no_stale "$ent_file" "Rocq 9\\.1" "Stale prover ref (Rocq 9.1)" || true
    fi
done
if [ "$QUICK_MODE" != "--quick" ]; then echo ""; fi

# ── Check hooks are installed ─────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking git hooks...${NC}"

    if [ -f "$REPO_ROOT/.git/hooks/pre-commit" ]; then
        if grep -q "riinac verify" "$REPO_ROOT/.git/hooks/pre-commit" 2>/dev/null; then
            echo -e "${GREEN}[OK]${NC} pre-commit hook installed (riinac verify)"
        else
            echo -e "${RED}[ERROR]${NC} pre-commit hook exists but is NOT the RIINA hook!"
            echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
            DISCREPANCIES=$((DISCREPANCIES + 1))
        fi
    else
        echo -e "${RED}[ERROR]${NC} pre-commit hook NOT installed!"
        echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
        DISCREPANCIES=$((DISCREPANCIES + 1))
    fi

    if [ -f "$REPO_ROOT/.git/hooks/pre-push" ]; then
        if grep -q "riinac verify" "$REPO_ROOT/.git/hooks/pre-push" 2>/dev/null; then
            echo -e "${GREEN}[OK]${NC} pre-push hook installed (riinac verify --full)"
        else
            echo -e "${RED}[ERROR]${NC} pre-push hook exists but is NOT the RIINA hook!"
            echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
            DISCREPANCIES=$((DISCREPANCIES + 1))
        fi
    else
        echo -e "${RED}[ERROR]${NC} pre-push hook NOT installed!"
        echo "         Run: bash 00_SETUP/scripts/install_hooks.sh"
        DISCREPANCIES=$((DISCREPANCIES + 1))
    fi
    echo ""
fi

# ── Count stale Tier 2 banners (informational) ───────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo -e "${CYAN}Checking Tier 2 banners...${NC}"

    STALE_BANNERS=0
    while IFS= read -r file; do
        # Skip Tier 3
        case "$file" in
            */01_RESEARCH/*|*/99_ARCHIVE/*|*/_archive_deprecated/*|*/CLAUDE_WEB_PROMPT_*|*/CLAUDE_AI_*|*/delegation_prompts/*) continue ;;
        esac
        banner_line=$(grep -E "^\*\*(Audit Update|Verification):\*\*" "$file" | head -1)
        # Check if banner has current Qed count
        if ! echo "$banner_line" | grep -q "${ACTUAL_QED_COMMA} Coq Qed" 2>/dev/null; then
            STALE_BANNERS=$((STALE_BANNERS + 1))
        fi
    done < <(grep -rlE "^\*\*(Audit Update|Verification):\*\*" "$REPO_ROOT" 2>/dev/null || true)

    if [ "$STALE_BANNERS" -gt 0 ]; then
        echo -e "${YELLOW}[WARN]${NC} $STALE_BANNERS files have stale verification banners"
        echo "         Run: bash scripts/sync-metrics.sh"
        WARNINGS=$((WARNINGS + 1))
    else
        echo -e "${GREEN}[OK]${NC} All verification banners are current"
    fi
    echo ""
fi

# ── Final report ──────────────────────────────────────────────────────

if [ "$QUICK_MODE" != "--quick" ]; then
    echo "================================================================"
fi
if [ "$DISCREPANCIES" -gt 0 ]; then
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "  ${RED}AUDIT FAILED${NC}"
        echo ""
        echo "  Discrepancies: $DISCREPANCIES"
        echo "  Warnings:      $WARNINGS"
        echo ""
        echo "  FIX ALL DISCREPANCIES BEFORE COMMITTING."
        echo "  Run: bash scripts/sync-metrics.sh"
        echo "================================================================"
    fi
    exit 1
elif [ "$WARNINGS" -gt 0 ]; then
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "  ${YELLOW}AUDIT PASSED WITH WARNINGS${NC}"
        echo ""
        echo "  Discrepancies: 0"
        echo "  Warnings:      $WARNINGS"
        echo ""
        echo "  Review warnings. Proceed with caution."
        echo "================================================================"
    fi
    exit 0
else
    if [ "$QUICK_MODE" != "--quick" ]; then
        echo -e "  ${GREEN}AUDIT PASSED${NC}"
        echo ""
        echo "  All documentation is current."
        echo "  Proceed with commit."
        echo "================================================================"
    fi
    exit 0
fi
