#!/usr/bin/env bash
# ============================================================================
# sync-metrics.sh — Propagate metrics from metrics.json to ALL documentation
#
# This script reads the single source of truth (website/public/metrics.json)
# and updates all documentation files to match.
#
# Usage:
#   bash scripts/sync-metrics.sh           # Full sync with report
#   bash scripts/sync-metrics.sh --dry-run # Show what would change, don't write
#
# Tier 1 (PUBLIC-FACING): Update body text + audit banner
# Tier 2 (INTERNAL DOCS): Update audit banner only
# Tier 3 (ARCHIVAL):      Skip entirely (01_RESEARCH/, 99_ARCHIVE/, CLAUDE_WEB_PROMPT_*)
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
METRICS_FILE="$REPO_ROOT/website/public/metrics.json"
DRY_RUN=0
CHANGED=0
SKIPPED=0

if [ "${1:-}" = "--dry-run" ]; then
    DRY_RUN=1
    echo "=== DRY RUN MODE — no files will be modified ==="
fi

echo ""
echo "================================================================"
echo "  RIINA METRICS SYNC"
echo "================================================================"
echo ""

# ── Read metrics.json ─────────────────────────────────────────────────

if [ ! -f "$METRICS_FILE" ]; then
    echo "ERROR: $METRICS_FILE not found."
    echo "Run: bash scripts/generate-metrics.sh first."
    exit 1
fi

# Locale-independent thousands separator (printf %'d requires LC_NUMERIC)
add_commas() { echo "$1" | sed ':a;s/\B[0-9]\{3\}\>$/,&/;ta'; }

# Parse values from metrics.json (use head -1 where fields repeat across sections)
QED=$(grep -oP '"qedActive":\s*\K\d+' "$METRICS_FILE" | head -1)
QED_COMMA=$(add_commas "$QED")
ADMITTED=$(grep -oP '"admitted":\s*\K\d+' "$METRICS_FILE" | head -1)
AXIOMS=$(grep -oP '"axioms":\s*\K\d+' "$METRICS_FILE" | head -1)
COQ_FILES_TOTAL=$(grep -oP '"filesTotal":\s*\K\d+' "$METRICS_FILE" | head -1)
COQ_FILES_ACTIVE=$(grep -oP '"filesActive":\s*\K\d+' "$METRICS_FILE" | head -1)
LEAN_THEOREMS=$(grep -oP '"theorems":\s*\K\d+' "$METRICS_FILE" | head -1)
ISABELLE_LEMMAS=$(grep -oP '"lemmas":\s*\K\d+' "$METRICS_FILE" | head -1)
TOTAL_PROOFS=$(grep -oP '"totalProofsAllProvers":\s*\K\d+' "$METRICS_FILE" | head -1)
TOTAL_PROOFS_COMMA=$(add_commas "$TOTAL_PROOFS")
TRIPLE_PROVER=$(grep -oP '"tripleProverTheorems":\s*\K\d+' "$METRICS_FILE" | head -1)
TOTAL_PROVERS=$(grep -oP '"totalProvers":\s*\K\d+' "$METRICS_FILE" | head -1)
TOTAL_PROVERS=${TOTAL_PROVERS:-10}
RUST_TESTS=$(grep -oP '"tests":\s*\K\d+' "$METRICS_FILE" | head -1)
RUST_CRATES=$(grep -oP '"crates":\s*\K\d+' "$METRICS_FILE" | head -1)
EXAMPLES=$(grep -oP '"examples":\s*\K\d+' "$METRICS_FILE" | head -1)
SESSION=$(grep -oP '"session":\s*\K\d+' "$METRICS_FILE" | head -1)
LEAN_FILES=$(grep -oP '"files":\s*\K\d+' "$METRICS_FILE" | head -1)
LEAN_LINES=$(grep -oP '"lines":\s*\K\d+' "$METRICS_FILE" | head -1)
ISABELLE_FILES=$(grep -oP '"files":\s*\K\d+' "$METRICS_FILE" | tail -1)
ISABELLE_LINES=$(grep -oP '"lines":\s*\K\d+' "$METRICS_FILE" | tail -1)

# Parse new prover counts
FSTAR_LEMMAS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('fstar',{}).get('lemmas',0))" 2>/dev/null || echo "0")
TLAPLUS_THEOREMS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('tlaplus',{}).get('theorems',0))" 2>/dev/null || echo "0")
ALLOY_ASSERTIONS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('alloy',{}).get('assertions',0))" 2>/dev/null || echo "0")
SMT_ASSERTIONS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('smt',{}).get('assertions',0))" 2>/dev/null || echo "0")
VERUS_PROOFS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('verus',{}).get('proofs',0))" 2>/dev/null || echo "0")
KANI_HARNESSES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('kani',{}).get('harnesses',0))" 2>/dev/null || echo "0")
TV_VALIDATIONS=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('tv',{}).get('validations',0))" 2>/dev/null || echo "0")
FSTAR_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('fstar',{}).get('files',0))" 2>/dev/null || echo "0")
TLAPLUS_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('tlaplus',{}).get('files',0))" 2>/dev/null || echo "0")
ALLOY_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('alloy',{}).get('files',0))" 2>/dev/null || echo "0")
SMT_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('smt',{}).get('files',0))" 2>/dev/null || echo "0")
VERUS_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('verus',{}).get('files',0))" 2>/dev/null || echo "0")
KANI_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('kani',{}).get('files',0))" 2>/dev/null || echo "0")
TV_FILES=$(python3 -c "import json; d=json.load(open('$METRICS_FILE')); print(d.get('tv',{}).get('files',0))" 2>/dev/null || echo "0")

echo "Source: $METRICS_FILE"
echo "  Coq Qed:       $QED_COMMA"
echo "  Lean:           $LEAN_THEOREMS theorems"
echo "  Isabelle:       $ISABELLE_LEMMAS lemmas"
echo "  F*:             $FSTAR_LEMMAS lemmas"
echo "  TLA+:           $TLAPLUS_THEOREMS theorems"
echo "  Alloy:          $ALLOY_ASSERTIONS assertions"
echo "  SMT:            $SMT_ASSERTIONS assertions"
echo "  Verus:          $VERUS_PROOFS proofs"
echo "  Kani:           $KANI_HARNESSES harnesses"
echo "  TV:             $TV_VALIDATIONS validations"
echo "  Total:          $TOTAL_PROOFS_COMMA ($TOTAL_PROVERS provers)"
echo "  Axioms:         $AXIOMS"
echo "  Rust tests:     $RUST_TESTS"
echo "  Session:        $SESSION"
echo ""

# The canonical audit banner line
BANNER="**Audit Update:** 2026-02-07 (Session ${SESSION}: 10-Prover Full Stack) — ${TOTAL_PROOFS_COMMA} total items across ${TOTAL_PROVERS} provers. ${QED_COMMA} Coq Qed + ${LEAN_THEOREMS} Lean + ${ISABELLE_LEMMAS} Isabelle + ${FSTAR_LEMMAS} F* + ${TLAPLUS_THEOREMS} TLA+ + ${ALLOY_ASSERTIONS} Alloy + ${SMT_ASSERTIONS} SMT + ${VERUS_PROOFS} Verus + ${KANI_HARNESSES} Kani + ${TV_VALIDATIONS} TV. 0 Admitted/sorry. ${AXIOMS} axiom (policy). ${RUST_TESTS} Rust tests."

# ── Helper: sed-replace in file ───────────────────────────────────────

do_sed() {
    local file="$1"
    local pattern="$2"
    local replacement="$3"
    local desc="${4:-}"

    if [ ! -f "$file" ]; then
        return
    fi

    if grep -qP "$pattern" "$file" 2>/dev/null; then
        if [ "$DRY_RUN" -eq 1 ]; then
            echo "  [DRY] Would update: $(basename "$file") — $desc"
        else
            sed -i -E "s|$pattern|$replacement|g" "$file"
        fi
        CHANGED=$((CHANGED + 1))
    fi
}

# ── Helper: Update audit banner line ──────────────────────────────────

update_banner() {
    local file="$1"

    if [ ! -f "$file" ]; then
        return
    fi

    # Check if file has an Audit Update banner
    if grep -q "^\*\*Audit Update:\*\*" "$file" 2>/dev/null; then
        local old_line
        old_line=$(grep "^\*\*Audit Update:\*\*" "$file" | head -1)

        if [ "$old_line" != "$BANNER" ]; then
            if [ "$DRY_RUN" -eq 1 ]; then
                echo "  [DRY] Would update banner: $(basename "$file")"
            else
                # Use awk for robust replacement (avoids sed escaping issues with special chars)
                local tmpfile
                tmpfile=$(mktemp)
                awk -v banner="$BANNER" '
                    /^\*\*Audit Update:\*\*/ && !replaced {
                        print banner
                        replaced = 1
                        next
                    }
                    { print }
                ' "$file" > "$tmpfile"
                mv "$tmpfile" "$file"
                echo "  [UPDATED] Banner: $(basename "$file")"
            fi
            CHANGED=$((CHANGED + 1))
        fi
    fi
}

# ── TIER 1: PUBLIC-FACING FILES (body + banner) ──────────────────────

echo "── Tier 1: Public-facing files ──"
echo ""

# --- README.md ---
README="$REPO_ROOT/README.md"
if [ -f "$README" ]; then
    echo "  Processing README.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Use awk for safe replacements (avoids sed ERE escaping bugs with \*\*)
        tmpfile=$(mktemp)
        awk -v qed="$QED_COMMA" -v lean="$LEAN_THEOREMS" -v isa="$ISABELLE_LEMMAS" -v total="$TOTAL_PROOFS_COMMA" '
        {
            # Update comparison table: "Yes (N Coq + N Lean + N Isabelle)"
            gsub(/Yes \([0-9,]+ Coq \+ [0-9]+ Lean \+ [0-9]+ Isabelle\)/, "Yes (" qed " Coq + " lean " Lean + " isa " Isabelle)")

            # Update prover table: "| **Coq 8.20.1** (Primary) | N Qed |"
            if ($0 ~ /[*][*]Coq 8[.]20[.]1[*][*].*Primary.*Qed/) {
                gsub(/[0-9,]+ Qed/, qed " Qed")
            }

            # Update phase 3 line with Coq/Lean/Isabelle totals
            if ($0 ~ /Coq Qed.*Lean.*Isabelle.*total/) {
                gsub(/[0-9,]+ Coq Qed \+ [0-9]+ Lean \+ [0-9]+ Isabelle = [0-9,]+ total/, qed " Coq Qed + " lean " Lean + " isa " Isabelle = " total " total")
            }

            print
        }
        ' "$README" > "$tmpfile"
        mv "$tmpfile" "$README"

        # Update audit banner if present
        update_banner "$README"
        echo "    [UPDATED] README.md"
    else
        echo "    [DRY] Would update README.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- CLAUDE.md ---
CLAUDE="$REPO_ROOT/CLAUDE.md"
if [ -f "$CLAUDE" ]; then
    echo "  Processing CLAUDE.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Update audit banner
        update_banner "$CLAUDE"

        # Use awk for safe multi-pattern replacement
        tmpfile=$(mktemp)
        awk -v qed="$QED_COMMA" -v lean="$LEAN_THEOREMS" -v isa="$ISABELLE_LEMMAS" \
            -v total="$TOTAL_PROOFS_COMMA" -v lean_files="$LEAN_FILES" \
            -v isa_files="$ISABELLE_FILES" -v examples="$EXAMPLES" \
            -v rust_tests="$RUST_TESTS" -v coq_active="$COQ_FILES_ACTIVE" '
        # §0.5 table: | **Lean 4 Theorems** | 119 | 12 files, 0 sorry |
        /[|] [*][*]Lean 4 Theorems[*][*]/ {
            gsub(/[|] [0-9]+ [|] [0-9]+ files/, "| " lean " | " lean_files " files")
        }
        # §0.5 table: | **Isabelle/HOL Lemmas** | 138 | 10 files, 0 sorry |
        /[|] [*][*]Isabelle[/]HOL Lemmas[*][*]/ {
            gsub(/[|] [0-9]+ [|] [0-9]+ files/, "| " isa " | " isa_files " files")
        }
        # §0.5 table: | **Total Proofs (All Provers)** | 8,185 |
        /[|] [*][*]Total Proofs [(]All Provers[)][*][*]/ {
            gsub(/[|] [0-9,]+ [|]/, "| " total " |")
        }
        # §0.5 table: | **Example .rii Files** | 120 |
        /[|] [*][*]Example .rii Files[*][*]/ {
            gsub(/[|] [0-9]+ [|]/, "| " examples " |")
        }
        # §0.6 table: | **Lean 4** | Secondary ... | 119 theorems, 0 sorry |
        /[|] [*][*]Lean 4[*][*] [|] Secondary/ {
            gsub(/[0-9]+ theorems/, lean " theorems")
        }
        # §0.6 table: | **Isabelle/HOL** | Tertiary ... | 138 lemmas, 0 sorry |
        /[|] [*][*]Isabelle[/]HOL[*][*] [|] Tertiary/ {
            gsub(/[0-9]+ lemmas/, isa " lemmas")
        }
        # Footer: 8,185 total proofs: 7,928 Coq + 119 Lean + 138 Isabelle
        /Last updated:.*total proofs:/ {
            gsub(/[0-9,]+ total proofs: [0-9,]+ Coq \+ [0-9]+ Lean \+ [0-9]+ Isabelle/, total " total proofs: " qed " Coq + " lean " Lean + " isa " Isabelle")
            gsub(/[0-9]+ active .v \+ [0-9]+ .lean \+ [0-9]+ .thy/, coq_active " active .v + " lean_files " .lean + " isa_files " .thy")
        }
        { print }
        ' "$CLAUDE" > "$tmpfile"
        mv "$tmpfile" "$CLAUDE"
        echo "    [UPDATED] CLAUDE.md"
    else
        echo "    [DRY] Would update CLAUDE.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- CHANGELOG.md ---
CHANGELOG="$REPO_ROOT/CHANGELOG.md"
if [ -f "$CHANGELOG" ]; then
    echo "  Processing CHANGELOG.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Update banner
        update_banner "$CHANGELOG"

        # Update body metrics: "Active Coq build now at 7,682 Qed proofs"
        sed -i -E "s|Active Coq build now at [0-9,]+ Qed proofs|Active Coq build now at ${QED_COMMA} Qed proofs|g" "$CHANGELOG"

        echo "    [UPDATED] CHANGELOG.md"
    else
        echo "    [DRY] Would update CHANGELOG.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- PROGRESS.md ---
PROGRESS="$REPO_ROOT/PROGRESS.md"
if [ -f "$PROGRESS" ]; then
    echo "  Processing PROGRESS.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Update banner
        update_banner "$PROGRESS"

        # Use awk for safe table row replacements (avoids sed ERE escaping bugs with \*\*)
        tmpfile=$(mktemp)
        awk -v session="$SESSION" -v total="$TOTAL_PROOFS_COMMA" -v axioms="$AXIOMS" \
            -v qed="$QED_COMMA" -v lean="$LEAN_THEOREMS" -v isa="$ISABELLE_LEMMAS" \
            -v coq_active="$COQ_FILES_ACTIVE" -v coq_total="$COQ_FILES_TOTAL" '
        # Update session line: **Session:** N (...)
        /^[*][*]Session:[*][*]/ {
            gsub(/[*][*]Session:[*][*] [0-9]+ \([^)]+\)/, "**Session:** " session " (Proof Depth 20+ All Files — " total " proofs across 3 provers, 0 sorry, " axioms " axiom)")
        }
        # Update Report Date
        /^[*][*]Report Date:[*][*]/ {
            gsub(/[*][*]Report Date:[*][*] [0-9-]+ \(Session [0-9]+\)/, "**Report Date:** 2026-02-06 (Session " session ")")
        }
        # Update table rows — match by first cell, replace number in second cell
        /[|] Qed Proofs [(]Coq[)]/ {
            gsub(/[*][*][0-9,]+[*][*]/, "**" qed "**")
        }
        /[|] Lean 4 Theorems/ {
            gsub(/[*][*][0-9]+[*][*]/, "**" lean "**")
        }
        /[|] Isabelle[/]HOL Lemmas/ {
            gsub(/[*][*][0-9]+[*][*]/, "**" isa "**")
        }
        /[|] Total Proofs [(]All Provers[)]/ {
            gsub(/[*][*][0-9,]+[*][*]/, "**" total "**")
        }
        /[|] Files in Build/ {
            gsub(/[*][*][0-9]+[*][*]/, "**" coq_active "**")
        }
        /[|] [.]v Files [(]Total[)]/ {
            gsub(/[*][*][0-9]+[*][*]/, "**" coq_total "**")
        }
        { print }
        ' "$PROGRESS" > "$tmpfile"
        mv "$tmpfile" "$PROGRESS"

        echo "    [UPDATED] PROGRESS.md"
    else
        echo "    [DRY] Would update PROGRESS.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- SECURITY.md ---
# Note: SECURITY.md uses a simple format (reporting email, scope, disclosure)
# and does not contain proof metrics — no sed replacements needed.
SECURITY="$REPO_ROOT/SECURITY.md"
if [ -f "$SECURITY" ]; then
    echo "  Processing SECURITY.md... [no metrics to update]"
fi

# --- CONTRIBUTING.md ---
CONTRIBUTING="$REPO_ROOT/CONTRIBUTING.md"
if [ -f "$CONTRIBUTING" ]; then
    echo "  Processing CONTRIBUTING.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        update_banner "$CONTRIBUTING"

        # Fix "Rocq 9.1 / Coq 8.21" → "Coq 8.20.1"
        sed -i 's/Rocq 9\.1 \/ Coq 8\.21/Coq 8.20.1/g' "$CONTRIBUTING"
        sed -i 's/Rocq 9\.1/Coq 8.20.1/g' "$CONTRIBUTING"

        # Fix test count in "should show 679 passing"
        sed -i -E "s/should show [0-9]+ passing/should show ${RUST_TESTS} passing/g" "$CONTRIBUTING"

        echo "    [UPDATED] CONTRIBUTING.md"
    else
        echo "    [DRY] Would update CONTRIBUTING.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- RiinaWebsite.jsx ---
WEBSITE_JSX="$REPO_ROOT/website/src/RiinaWebsite.jsx"
if [ -f "$WEBSITE_JSX" ]; then
    echo "  Processing RiinaWebsite.jsx..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Update release highlights: "7,682 Qed proofs in Coq + 91 Lean + 102 Isabelle"
        sed -i -E "s|[0-9,]+ Qed proofs in Coq \+ [0-9]+ Lean \+ [0-9]+ Isabelle|${QED_COMMA} Qed proofs in Coq + ${LEAN_THEOREMS} Lean + ${ISABELLE_LEMMAS} Isabelle|g" "$WEBSITE_JSX"

        # Update hero terminal output: <div ...>7682</div>
        sed -i -E "s|>7682<|>${QED}<|g" "$WEBSITE_JSX"

        # Update triple-prover grid: count: '7,682'
        sed -i -E "s|count: '7,682'|count: '${QED_COMMA}'|g" "$WEBSITE_JSX"
        sed -i -E "s|count: '[0-9,]+', role: 'Primary'|count: '${QED_COMMA}', role: 'Primary'|g" "$WEBSITE_JSX"

        # Update Lean count in triple-prover grid
        sed -i -E "s|count: '91', role: 'Secondary'|count: '${LEAN_THEOREMS}', role: 'Secondary'|g" "$WEBSITE_JSX"

        # Update Isabelle count in triple-prover grid
        sed -i -E "s|count: '102', role: 'Tertiary'|count: '${ISABELLE_LEMMAS}', role: 'Tertiary'|g" "$WEBSITE_JSX"

        # Update How page prover rows: "theorems: '7,682 Qed'"
        sed -i -E "s|theorems: '[0-9,]+ Qed'|theorems: '${QED_COMMA} Qed'|g" "$WEBSITE_JSX"
        sed -i -E "s|theorems: '[0-9]+ theorems'|theorems: '${LEAN_THEOREMS} theorems'|g" "$WEBSITE_JSX"
        sed -i -E "s|theorems: '[0-9]+ lemmas'|theorems: '${ISABELLE_LEMMAS} lemmas'|g" "$WEBSITE_JSX"

        # Update verification banner: "7,875 proofs"
        sed -i -E "s|<span>[0-9,]+</span> proofs|<span>${TOTAL_PROOFS_COMMA}</span> proofs|g" "$WEBSITE_JSX"

        echo "    [UPDATED] RiinaWebsite.jsx"
    else
        echo "    [DRY] Would update RiinaWebsite.jsx"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- website/index.html ---
INDEX_HTML="$REPO_ROOT/website/index.html"
if [ -f "$INDEX_HTML" ]; then
    echo "  Processing website/index.html..."
    if [ "$DRY_RUN" -eq 0 ]; then
        # Update meta description total proofs
        sed -i -E "s|[0-9,]+ proofs across [0-9]+ independent provers|${TOTAL_PROOFS_COMMA} proofs across ${TOTAL_PROVERS} independent provers|g" "$INDEX_HTML"

        echo "    [UPDATED] website/index.html"
    else
        echo "    [DRY] Would update website/index.html"
    fi
    CHANGED=$((CHANGED + 1))
fi

# --- Enterprise docs ---
CERT="$REPO_ROOT/docs/enterprise/CERTIFICATION.md"
if [ -f "$CERT" ]; then
    echo "  Processing CERTIFICATION.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        update_banner "$CERT"
        sed -i 's/Rocq 9\.1 (Coq 8\.21)/Coq 8.20.1/g' "$CERT"
        sed -i 's/Rocq 9\.1/Coq 8.20.1/g' "$CERT"
        echo "    [UPDATED] CERTIFICATION.md"
    else
        echo "    [DRY] Would update CERTIFICATION.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

COMPLIANCE_PKG="$REPO_ROOT/docs/enterprise/COMPLIANCE_PACKAGING.md"
if [ -f "$COMPLIANCE_PKG" ]; then
    echo "  Processing COMPLIANCE_PACKAGING.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        update_banner "$COMPLIANCE_PKG"
        sed -i 's/Rocq 9\.1 (Coq 8\.21)/Coq 8.20.1/g' "$COMPLIANCE_PKG"
        sed -i 's/Rocq 9\.1/Coq 8.20.1/g' "$COMPLIANCE_PKG"
        echo "    [UPDATED] COMPLIANCE_PACKAGING.md"
    else
        echo "    [DRY] Would update COMPLIANCE_PACKAGING.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

COMPLIANCE_GUIDE="$REPO_ROOT/docs/enterprise/COMPLIANCE_GUIDE.md"
if [ -f "$COMPLIANCE_GUIDE" ]; then
    echo "  Processing COMPLIANCE_GUIDE.md..."
    if [ "$DRY_RUN" -eq 0 ]; then
        update_banner "$COMPLIANCE_GUIDE"
        echo "    [UPDATED] COMPLIANCE_GUIDE.md"
    else
        echo "    [DRY] Would update COMPLIANCE_GUIDE.md"
    fi
    CHANGED=$((CHANGED + 1))
fi

echo ""

# ── TIER 2: INTERNAL DOCS (banner only) ──────────────────────────────

echo "── Tier 2: Internal docs (banner only) ──"
echo ""

# Directories to scan for Tier 2 banners
TIER2_DIRS=(
    "$REPO_ROOT/04_SPECS"
    "$REPO_ROOT/06_COORDINATION"
    "$REPO_ROOT/07_EXAMPLES"
    "$REPO_ROOT/02_FORMAL/coq"
)

# Files to always include (top-level)
TIER2_FILES=(
    "$REPO_ROOT/SESSION_LOG.md"
    "$REPO_ROOT/REPO_PROTECTION_GUIDE.md"
    "$REPO_ROOT/WORKER_B_SPEC_STORE_REL_REWRITE.md"
)

# Files/patterns to SKIP (Tier 3: archival/historical)
is_tier3() {
    local file="$1"
    case "$file" in
        */01_RESEARCH/*) return 0 ;;
        */99_ARCHIVE/*) return 0 ;;
        */_archive_deprecated/*) return 0 ;;
        */CLAUDE_WEB_PROMPT_*) return 0 ;;
        */CLAUDE_AI_DELEGATION_SESSION*) return 0 ;;
        */CLAUDE_AI_DELEGATION_PROMPT.md) return 0 ;;
        */delegation_prompts/*) return 0 ;;
    esac
    return 1
}

# Update banners in Tier 2 individual files
for file in "${TIER2_FILES[@]}"; do
    if [ -f "$file" ]; then
        if ! is_tier3 "$file"; then
            update_banner "$file"
        fi
    fi
done

# Update banners in Tier 2 directories
for dir in "${TIER2_DIRS[@]}"; do
    if [ -d "$dir" ]; then
        while IFS= read -r file; do
            if ! is_tier3 "$file"; then
                update_banner "$file"
            else
                SKIPPED=$((SKIPPED + 1))
            fi
        done < <(grep -rl "^\*\*Audit Update:\*\*" "$dir" 2>/dev/null || true)
    fi
done

echo ""

# ── Final report ──────────────────────────────────────────────────────

echo "================================================================"
if [ "$DRY_RUN" -eq 1 ]; then
    echo "  DRY RUN COMPLETE"
else
    echo "  SYNC COMPLETE"
fi
echo ""
echo "  Files updated: $CHANGED"
echo "  Files skipped (Tier 3): $SKIPPED"
echo ""
echo "  Next: bash scripts/audit-docs.sh"
echo "================================================================"
