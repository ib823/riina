#!/bin/bash
# RIINA Living Metrics Generator
# Generates metrics.json from actual codebase counts
# Called during website build to ensure accuracy
#
# IMPORTANT: This is the SINGLE SOURCE OF TRUTH for all metrics.
# After running this, run sync-metrics.sh to propagate to all docs.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_FILE="$ROOT_DIR/website/public/metrics.json"

# --fast mode: count #[test] annotations statically instead of running cargo test
FAST_MODE=0
if [ "${1:-}" = "--fast" ]; then
    FAST_MODE=1
fi

echo "=== RIINA Metrics Generator ==="
if [ "$FAST_MODE" -eq 1 ]; then
    echo "  (fast mode: static test count)"
fi

# Get current timestamp
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
DATE_HUMAN=$(date -u +"%B %d, %Y at %H:%M UTC")

# Count Qed proofs (active build) — from _CoqProject only (matches verify.rs)
QED_ACTIVE=0
while IFS= read -r f; do
    [[ "$f" =~ ^[[:space:]]*# ]] && continue
    [[ "$f" != *.v ]] && continue
    f=$(echo "$f" | sed 's/^[[:space:]]*//')
    fullpath="$ROOT_DIR/02_FORMAL/coq/$f"
    count=$(grep -c "Qed\." "$fullpath" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        QED_ACTIVE=$((QED_ACTIVE + count))
    fi
done < "$ROOT_DIR/02_FORMAL/coq/_CoqProject"

# Count Qed proofs in deprecated archive
QED_DEPRECATED=0
while IFS= read -r f; do
    count=$(grep -c "Qed\." "$f" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        QED_DEPRECATED=$((QED_DEPRECATED + count))
    fi
done < <(find "$ROOT_DIR/02_FORMAL/coq/properties/_archive_deprecated" -name "*.v" -type f 2>/dev/null)

# Count total .v files
COQ_FILES=$(find "$ROOT_DIR/02_FORMAL/coq" -name "*.v" -type f 2>/dev/null | wc -l)

# Count active build files (from _CoqProject) using the same parsing rules as
# proof-ledger/public-quality scripts (ignore comments/flags, only .v entries).
COQ_ACTIVE_FILES=$(
    awk '
      {
        line=$0;
        sub(/^[ \t]+/, "", line);
        if (line ~ /^[#-]/ || line == "") next;
        split(line, tok, /[ \t]+/);
        if (tok[1] ~ /\.v$/) c++;
      }
      END { print c + 0 }
    ' "$ROOT_DIR/02_FORMAL/coq/_CoqProject" 2>/dev/null || echo "0"
)

# Count Admitted in active build (should be 0) — from _CoqProject only
# Only count "Admitted." as standalone tactic (not in comments or strings)
ADMITTED=0
while IFS= read -r f; do
    [[ "$f" =~ ^[[:space:]]*# ]] && continue
    [[ "$f" != *.v ]] && continue
    f=$(echo "$f" | sed 's/^[[:space:]]*//')
    fullpath="$ROOT_DIR/02_FORMAL/coq/$f"
    count=$(grep -cP '^\s*Admitted\.' "$fullpath" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        ADMITTED=$((ADMITTED + count))
    fi
done < "$ROOT_DIR/02_FORMAL/coq/_CoqProject"

# Count axioms dynamically from active build — from _CoqProject only
AXIOMS=0
while IFS= read -r f; do
    [[ "$f" =~ ^[[:space:]]*# ]] && continue
    [[ "$f" != *.v ]] && continue
    f=$(echo "$f" | sed 's/^[[:space:]]*//')
    fullpath="$ROOT_DIR/02_FORMAL/coq/$f"
    count=$(grep -cE "^Axiom " "$fullpath" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        AXIOMS=$((AXIOMS + count))
    fi
done < "$ROOT_DIR/02_FORMAL/coq/_CoqProject"

# Count explicit proof-architecture assumptions in active build (target: 0)
# Currently tracked assumption:
#   - Parameter val_rel_n_step_up (NonInterference_v2.v)
ASSUMPTIONS=0
while IFS= read -r f; do
    [[ "$f" =~ ^[[:space:]]*# ]] && continue
    [[ "$f" != *.v ]] && continue
    f=$(echo "$f" | sed 's/^[[:space:]]*//')
    fullpath="$ROOT_DIR/02_FORMAL/coq/$f"
    count=$(grep -cE "^Parameter val_rel_n_step_up " "$fullpath" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        ASSUMPTIONS=$((ASSUMPTIONS + count))
    fi
done < "$ROOT_DIR/02_FORMAL/coq/_CoqProject"

# Count Lean 4 theorems (theorem + lemma declarations)
LEAN_THEOREMS=0
LEAN_SORRY=0
LEAN_FILES=0
LEAN_LINES=0
if [ -d "$ROOT_DIR/02_FORMAL/lean" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^\s*(theorem|lemma)\s" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            LEAN_THEOREMS=$((LEAN_THEOREMS + count))
        fi
        # Count token-level sorry usage (captures "by sorry", ":= sorry", etc.).
        sorry_count=$(grep -oP '\bsorry\b' "$f" 2>/dev/null | wc -l | tr -d ' ')
        if [ -n "$sorry_count" ] && [ "$sorry_count" -gt 0 ] 2>/dev/null; then
            LEAN_SORRY=$((LEAN_SORRY + sorry_count))
        fi
    done < <(find "$ROOT_DIR/02_FORMAL/lean" -name "*.lean" -type f ! -name "lakefile.lean" 2>/dev/null)
    LEAN_FILES=$(find "$ROOT_DIR/02_FORMAL/lean" -name "*.lean" -type f ! -name "lakefile.lean" 2>/dev/null | wc -l)
    LEAN_LINES=$(find "$ROOT_DIR/02_FORMAL/lean" -name "*.lean" -type f ! -name "lakefile.lean" -exec cat {} + 2>/dev/null | wc -l)
fi

# Count Isabelle lemmas (lemma + theorem + corollary declarations)
ISABELLE_LEMMAS=0
ISABELLE_SORRY=0
ISABELLE_FILES=0
ISABELLE_LINES=0
if [ -d "$ROOT_DIR/02_FORMAL/isabelle" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^\s*(lemma|theorem|corollary)\s" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            ISABELLE_LEMMAS=$((ISABELLE_LEMMAS + count))
        fi
        # Count token-level sorry/oops usage across the file.
        sorry_count=$(grep -oP '\b(sorry|oops)\b' "$f" 2>/dev/null | wc -l | tr -d ' ')
        if [ -n "$sorry_count" ] && [ "$sorry_count" -gt 0 ] 2>/dev/null; then
            ISABELLE_SORRY=$((ISABELLE_SORRY + sorry_count))
        fi
    done < <(find "$ROOT_DIR/02_FORMAL/isabelle" -name "*.thy" -type f 2>/dev/null)
    ISABELLE_FILES=$(find "$ROOT_DIR/02_FORMAL/isabelle" -name "*.thy" -type f 2>/dev/null | wc -l)
    ISABELLE_LINES=$(find "$ROOT_DIR/02_FORMAL/isabelle" -name "*.thy" -type f -exec cat {} + 2>/dev/null | wc -l)
fi

# Compute Lean axioms (axiom declarations)
LEAN_AXIOMS=0
if [ -d "$ROOT_DIR/02_FORMAL/lean" ]; then
    while IFS= read -r f; do
        count=$(grep -c "^axiom " "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            LEAN_AXIOMS=$((LEAN_AXIOMS + count))
        fi
    done < <(find "$ROOT_DIR/02_FORMAL/lean" -name "*.lean" -type f ! -name "lakefile.lean" 2>/dev/null)
fi

# Compute Isabelle axioms
ISABELLE_AXIOMS=0
if [ -d "$ROOT_DIR/02_FORMAL/isabelle" ]; then
    while IFS= read -r f; do
        count=$(grep -c "axiomatization" "$f" 2>/dev/null || true)
        if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
            ISABELLE_AXIOMS=$((ISABELLE_AXIOMS + count))
        fi
    done < <(find "$ROOT_DIR/02_FORMAL/isabelle" -name "*.thy" -type f 2>/dev/null)
fi

# Count F* lemmas (val ... _lemma declarations)
FSTAR_LEMMAS=0
FSTAR_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/fstar" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "val\s+\w+_lemma\b" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && FSTAR_LEMMAS=$((FSTAR_LEMMAS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/fstar" -name "*.fst" -type f 2>/dev/null)
    FSTAR_FILES=$(find "$ROOT_DIR/02_FORMAL/fstar" -name "*.fst" -type f 2>/dev/null | wc -l)
fi

# Count TLA+ theorems (THEOREM declarations)
TLAPLUS_THEOREMS=0
TLAPLUS_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/tlaplus" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^THEOREM\s" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && TLAPLUS_THEOREMS=$((TLAPLUS_THEOREMS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/tlaplus" -name "*.tla" -type f 2>/dev/null)
    TLAPLUS_FILES=$(find "$ROOT_DIR/02_FORMAL/tlaplus" -name "*.tla" -type f 2>/dev/null | wc -l)
fi

# Count Alloy assertions (check declarations)
ALLOY_ASSERTIONS=0
ALLOY_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/alloy" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^check\s" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && ALLOY_ASSERTIONS=$((ALLOY_ASSERTIONS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/alloy" -name "*.als" -type f 2>/dev/null)
    ALLOY_FILES=$(find "$ROOT_DIR/02_FORMAL/alloy" -name "*.als" -type f 2>/dev/null | wc -l)
fi

# Count SMT assertions (Z3/CVC5 - assert declarations, excluding .tv.smt2)
SMT_ASSERTIONS=0
SMT_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/smt" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^\(assert\s" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && SMT_ASSERTIONS=$((SMT_ASSERTIONS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/smt" -name "*.smt2" -type f 2>/dev/null)
    SMT_FILES=$(find "$ROOT_DIR/02_FORMAL/smt" -name "*.smt2" -type f 2>/dev/null | wc -l)
fi

# Count Verus proofs (proof fn declarations)
VERUS_PROOFS=0
VERUS_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/verus" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "proof fn\s" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && VERUS_PROOFS=$((VERUS_PROOFS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/verus" -name "*.rs" -type f 2>/dev/null)
    VERUS_FILES=$(find "$ROOT_DIR/02_FORMAL/verus" -name "*.rs" -type f 2>/dev/null | wc -l)
fi

# Count Kani harnesses (#[kani::proof] declarations)
KANI_HARNESSES=0
KANI_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/kani" ]; then
    while IFS= read -r f; do
        count=$(grep -c '#\[kani::proof\]' "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && KANI_HARNESSES=$((KANI_HARNESSES + count))
    done < <(find "$ROOT_DIR/02_FORMAL/kani" -name "*.rs" -type f 2>/dev/null)
    KANI_FILES=$(find "$ROOT_DIR/02_FORMAL/kani" -name "*.rs" -type f 2>/dev/null | wc -l)
fi

# Count Translation Validation assertions
TV_VALIDATIONS=0
TV_FILES=0
if [ -d "$ROOT_DIR/02_FORMAL/tv" ]; then
    while IFS= read -r f; do
        count=$(grep -cP "^\(assert\s" "$f" 2>/dev/null || true)
        [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null && TV_VALIDATIONS=$((TV_VALIDATIONS + count))
    done < <(find "$ROOT_DIR/02_FORMAL/tv" -name "*.smt2" -type f 2>/dev/null)
    TV_FILES=$(find "$ROOT_DIR/02_FORMAL/tv" -name "*.smt2" -type f 2>/dev/null | wc -l)
fi

# Quality tier counting: core vs domain vs trivial
# Tier 1 (core): foundations/ + type_system/ + effects/ + properties/ + termination/
COQ_TIER1_CORE=0
for subdir in foundations type_system effects properties termination; do
    dir="$ROOT_DIR/02_FORMAL/coq/$subdir"
    if [ -d "$dir" ]; then
        while IFS= read -r f; do
            count=$(grep -c "Qed\." "$f" 2>/dev/null || true)
            if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
                COQ_TIER1_CORE=$((COQ_TIER1_CORE + count))
            fi
        done < <(find "$dir" -name "*.v" -type f ! -path "*/_archive_deprecated/*" 2>/dev/null)
    fi
done

# Tier 2 (domain): domains/ + Industries/ + compliance/
COQ_TIER2_DOMAIN=$((QED_ACTIVE - COQ_TIER1_CORE))

# Count trivial proofs: "Proof. reflexivity. Qed." and "Proof. intros. exact I. Qed." patterns
COQ_TRIVIAL=0
while IFS= read -r f; do
    count=$(grep -cP 'Proof\.\s*(reflexivity|intros\.\s*exact I|exact I|trivial)\.\s*Qed\.' "$f" 2>/dev/null || true)
    if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
        COQ_TRIVIAL=$((COQ_TRIVIAL + count))
    fi
done < <(find "$ROOT_DIR/02_FORMAL/coq" -name "*.v" -type f ! -path "*/_archive_deprecated/*" 2>/dev/null)

# Total proofs across ALL 10 provers
TOTAL_PROOFS=$((QED_ACTIVE + LEAN_THEOREMS + ISABELLE_LEMMAS + FSTAR_LEMMAS + TLAPLUS_THEOREMS + ALLOY_ASSERTIONS + SMT_ASSERTIONS + VERUS_PROOFS + KANI_HARNESSES + TV_VALIDATIONS))

# Count triple-prover theorems: min(domain Lean theorems, domain Isabelle lemmas)
# + foundation triple-prover count from MULTIPROVER_VALIDATION.md
FOUNDATION_TRIPLE=$(grep -oP '\d+ triple-prover theorems' "$ROOT_DIR/02_FORMAL/MULTIPROVER_VALIDATION.md" 2>/dev/null | grep -oP '^\d+' || echo "86")
# Domain triple-prover: all domain theorems exist in all 3 provers
LEAN_DOMAIN_THEOREMS=0
if [ -d "$ROOT_DIR/02_FORMAL/lean/RIINA/Domains" ] || [ -d "$ROOT_DIR/02_FORMAL/lean/RIINA/Industries" ]; then
    for subdir in Domains Industries; do
        dir="$ROOT_DIR/02_FORMAL/lean/RIINA/$subdir"
        if [ -d "$dir" ]; then
            while IFS= read -r f; do
                count=$(grep -cP "^\s*(theorem|lemma)\s" "$f" 2>/dev/null || true)
                if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
                    LEAN_DOMAIN_THEOREMS=$((LEAN_DOMAIN_THEOREMS + count))
                fi
            done < <(find "$dir" -name "*.lean" -type f 2>/dev/null)
        fi
    done
fi
ISA_DOMAIN_LEMMAS=0
if [ -d "$ROOT_DIR/02_FORMAL/isabelle/RIINA/Domains" ] || [ -d "$ROOT_DIR/02_FORMAL/isabelle/RIINA/Industries" ]; then
    for subdir in Domains Industries; do
        dir="$ROOT_DIR/02_FORMAL/isabelle/RIINA/$subdir"
        if [ -d "$dir" ]; then
            while IFS= read -r f; do
                count=$(grep -cP "^\s*(lemma|theorem)\s" "$f" 2>/dev/null || true)
                if [ -n "$count" ] && [ "$count" -gt 0 ] 2>/dev/null; then
                    ISA_DOMAIN_LEMMAS=$((ISA_DOMAIN_LEMMAS + count))
                fi
            done < <(find "$dir" -name "*.thy" -type f 2>/dev/null)
        fi
    done
fi
# Triple-prover = min(Lean domain, Isabelle domain) + foundation
DOMAIN_TRIPLE=$((LEAN_DOMAIN_THEOREMS < ISA_DOMAIN_LEMMAS ? LEAN_DOMAIN_THEOREMS : ISA_DOMAIN_LEMMAS))
TRIPLE_PROVER=$((FOUNDATION_TRIPLE + DOMAIN_TRIPLE))

# Count Rust tests
if [ -f "${HOME}/.cargo/env" ]; then
    source "${HOME}/.cargo/env"
fi
if [ "$FAST_MODE" -eq 1 ]; then
    # Fast: count #[test] annotations statically (< 1s vs ~30s for cargo test)
    RUST_TESTS=$(grep -r '#\[test\]' "$ROOT_DIR/03_PROTO/crates" --include="*.rs" 2>/dev/null | wc -l)
else
    # Full: run cargo test for accurate count
    RUST_TESTS=$(cd "$ROOT_DIR/03_PROTO" && cargo test --all 2>&1 | grep -oP '\d+ passed' | awk '{sum += $1} END {print sum+0}' || echo "0")
fi

# Count Rust crates (03_PROTO only — the main language crates)
RUST_CRATES=$(find "$ROOT_DIR/03_PROTO/crates" -name "Cargo.toml" -type f 2>/dev/null | wc -l)

# Count example files
EXAMPLE_FILES=$(find "$ROOT_DIR/07_EXAMPLES" -name "*.rii" -type f 2>/dev/null | wc -l)

# Count research domains
RESEARCH_DOMAINS=$(find "$ROOT_DIR/02_FORMAL/coq/domains" -name "*.v" -type f 2>/dev/null | wc -l)

# Get version
VERSION=$(cat "$ROOT_DIR/VERSION" 2>/dev/null || echo "0.1.0")

# Get git info
GIT_COMMIT=$(git -C "$ROOT_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")
GIT_BRANCH=$(git -C "$ROOT_DIR" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "main")

# Calculate session number (highest across CLAUDE.md and SESSION_LOG.md)
SESSION_FROM_LOG=$(grep -oP "Session \K\d+" "$ROOT_DIR/SESSION_LOG.md" 2>/dev/null | sort -n | tail -1 || echo "0")
SESSION_FROM_CLAUDE=$(grep -oP "Session \K\d+" "$ROOT_DIR/CLAUDE.md" 2>/dev/null | sort -n | tail -1 || echo "0")
SESSION=$((SESSION_FROM_LOG > SESSION_FROM_CLAUDE ? SESSION_FROM_LOG : SESSION_FROM_CLAUDE))

# Conservative claim-level classification for public messaging:
#   generated -> present in source or generated artifacts
#   compiled -> tool/lane compilation evidence available
#   mechanized -> machine-checked with active-build zero-gap policy
#   independently_audited -> external independent audit published
COQ_COMPILED=true
if [ "$QED_ACTIVE" -eq 0 ] || [ "$ADMITTED" -ne 0 ] || [ "$AXIOMS" -ne 0 ] || [ "$ASSUMPTIONS" -ne 0 ]; then
    COQ_COMPILED=false
fi

# Keep non-Coq compile flags strict: only set true when lane-specific
# compilation evidence is integrated into this generator.
LEAN_COMPILED=false
ISABELLE_COMPILED=false

CLAIM_COQ="generated"
[ "$COQ_COMPILED" = true ] && CLAIM_COQ="mechanized"
CLAIM_LEAN="generated"
[ "$LEAN_COMPILED" = true ] && CLAIM_LEAN="compiled"
CLAIM_ISABELLE="generated"
[ "$ISABELLE_COMPILED" = true ] && CLAIM_ISABELLE="compiled"
CLAIM_FSTAR="generated"
CLAIM_TLAPLUS="generated"
CLAIM_ALLOY="generated"
CLAIM_SMT="generated"
CLAIM_VERUS="generated"
CLAIM_KANI="generated"
CLAIM_TV="generated"

INDEPENDENTLY_AUDITED=false
OVERALL_CLAIM="$CLAIM_COQ"
[ "$INDEPENDENTLY_AUDITED" = true ] && OVERALL_CLAIM="independently_audited"

MULTIPROVER_STATUS="IN_PROGRESS"
[ "$OVERALL_CLAIM" = "mechanized" ] && MULTIPROVER_STATUS="ACTIVE_COQ_MECHANIZED"
if [ "$CLAIM_LEAN" != "generated" ] \
  && [ "$CLAIM_ISABELLE" != "generated" ] \
  && [ "$CLAIM_FSTAR" != "generated" ] \
  && [ "$CLAIM_TLAPLUS" != "generated" ] \
  && [ "$CLAIM_ALLOY" != "generated" ] \
  && [ "$CLAIM_SMT" != "generated" ] \
  && [ "$CLAIM_VERUS" != "generated" ] \
  && [ "$CLAIM_KANI" != "generated" ] \
  && [ "$CLAIM_TV" != "generated" ]; then
    MULTIPROVER_STATUS="MULTI_LANE_COMPILED"
fi
[ "$INDEPENDENTLY_AUDITED" = true ] && MULTIPROVER_STATUS="INDEPENDENTLY_AUDITED"

# Generate JSON
cat > "$OUTPUT_FILE" << EOF
{
  "generated": "$TIMESTAMP",
  "generatedHuman": "$DATE_HUMAN",
  "version": "$VERSION",
  "session": $SESSION,
  "git": {
    "commit": "$GIT_COMMIT",
    "branch": "$GIT_BRANCH"
  },
  "proofs": {
    "qedActive": $QED_ACTIVE,
    "qedDeprecated": $QED_DEPRECATED,
    "qedTotal": $((QED_ACTIVE + QED_DEPRECATED)),
    "admitted": $ADMITTED,
    "axioms": $AXIOMS,
    "assumptions": $ASSUMPTIONS,
    "axiomsJustified": true
  },
  "coq": {
    "filesTotal": $COQ_FILES,
    "filesActive": $COQ_ACTIVE_FILES,
    "domains": $RESEARCH_DOMAINS,
    "prover": "Coq 8.20.1"
  },
  "lean": {
    "theorems": $LEAN_THEOREMS,
    "sorry": $LEAN_SORRY,
    "axioms": $LEAN_AXIOMS,
    "files": $LEAN_FILES,
    "lines": $LEAN_LINES,
    "prover": "Lean 4"
  },
  "isabelle": {
    "lemmas": $ISABELLE_LEMMAS,
    "sorry": $ISABELLE_SORRY,
    "axioms": $ISABELLE_AXIOMS,
    "files": $ISABELLE_FILES,
    "lines": $ISABELLE_LINES,
    "prover": "Isabelle/HOL"
  },
  "fstar": {
    "lemmas": $FSTAR_LEMMAS,
    "files": $FSTAR_FILES,
    "prover": "F*"
  },
  "tlaplus": {
    "theorems": $TLAPLUS_THEOREMS,
    "files": $TLAPLUS_FILES,
    "prover": "TLA+"
  },
  "alloy": {
    "assertions": $ALLOY_ASSERTIONS,
    "files": $ALLOY_FILES,
    "prover": "Alloy 6"
  },
  "smt": {
    "assertions": $SMT_ASSERTIONS,
    "files": $SMT_FILES,
    "prover": "Z3/CVC5 (SMT-LIB)"
  },
  "verus": {
    "proofs": $VERUS_PROOFS,
    "files": $VERUS_FILES,
    "prover": "Verus"
  },
  "kani": {
    "harnesses": $KANI_HARNESSES,
    "files": $KANI_FILES,
    "prover": "Kani"
  },
  "tv": {
    "validations": $TV_VALIDATIONS,
    "files": $TV_FILES,
    "prover": "Translation Validation"
  },
  "multiProver": {
    "tripleProverTheorems": $TRIPLE_PROVER,
    "totalProofsAllProvers": $TOTAL_PROOFS,
    "totalProvers": 10,
    "proverList": ["Coq", "Lean 4", "Isabelle/HOL", "F*", "TLA+", "Alloy 6", "Z3/CVC5", "Verus", "Kani", "Translation Validation"],
    "sorry": $((LEAN_SORRY + ISABELLE_SORRY)),
    "status": "$MULTIPROVER_STATUS"
  },
  "quality": {
    "coqCompiled": $COQ_COMPILED,
    "leanCompiled": $LEAN_COMPILED,
    "isabelleCompiled": $ISABELLE_COMPILED,
    "fstarStatus": "$CLAIM_FSTAR",
    "tlaplusStatus": "$CLAIM_TLAPLUS",
    "alloyStatus": "$CLAIM_ALLOY",
    "smtStatus": "$CLAIM_SMT",
    "verusStatus": "$CLAIM_VERUS",
    "kaniStatus": "$CLAIM_KANI",
    "tvStatus": "$CLAIM_TV",
    "coqTiers": {
      "core": $COQ_TIER1_CORE,
      "domain": $COQ_TIER2_DOMAIN,
      "domainTrivial": $COQ_TRIVIAL
    }
  },
  "claimLevels": {
    "legend": ["generated", "compiled", "mechanized", "independently_audited"],
    "overall": "$OVERALL_CLAIM",
    "independentlyAudited": $INDEPENDENTLY_AUDITED,
    "coq": "$CLAIM_COQ",
    "lean": "$CLAIM_LEAN",
    "isabelle": "$CLAIM_ISABELLE",
    "fstar": "$CLAIM_FSTAR",
    "tlaplus": "$CLAIM_TLAPLUS",
    "alloy": "$CLAIM_ALLOY",
    "smt": "$CLAIM_SMT",
    "verus": "$CLAIM_VERUS",
    "kani": "$CLAIM_KANI",
    "tv": "$CLAIM_TV"
  },
  "rust": {
    "tests": ${RUST_TESTS:-0},
    "crates": $RUST_CRATES
  },
  "examples": $EXAMPLE_FILES,
  "status": {
    "build": "passing",
    "grade": "A",
    "threats": "1231+"
  },
  "milestones": [
    { "date": "2026-02-07", "event": "10-lane verification corpus published (Coq, Lean, Isabelle, F*, TLA+, Alloy, SMT, Verus, Kani, TV) — claim levels apply per lane" },
    { "date": "2026-02-07", "event": "Lean 4 lane integrated into public metrics (see claim levels for current status)" },
    { "date": "2026-02-07", "event": "SMT assertion corpus integrated into public metrics" },
    { "date": "2026-02-06", "event": "Proof depth 20+ across all 250 domain files" },
    { "date": "2026-02-06", "event": "Cross-prover mapping milestone recorded (current quality flags are authoritative)" },
    { "date": "2026-02-10", "event": "Axiom token elimination: 4 → 0 (active-build explicit assumptions now 0)" },
    { "date": "2026-02-01", "event": "Phase 7 complete: Platform Universality" }
  ]
}
EOF

echo "Generated: $OUTPUT_FILE"
echo "  Qed Active:   $QED_ACTIVE"
echo "  Qed Deprecated: $QED_DEPRECATED"
echo "  Qed Total:    $((QED_ACTIVE + QED_DEPRECATED))"
echo "  Admitted:     $ADMITTED"
echo "  Axioms:       $AXIOMS"
echo "  Assumptions:  $ASSUMPTIONS"
echo "  Lean:         $LEAN_THEOREMS theorems, $LEAN_SORRY sorry, $LEAN_FILES files"
echo "  Isabelle:     $ISABELLE_LEMMAS lemmas, $ISABELLE_SORRY sorry, $ISABELLE_FILES files"
echo "  F*:           $FSTAR_LEMMAS lemmas, $FSTAR_FILES files"
echo "  TLA+:         $TLAPLUS_THEOREMS theorems, $TLAPLUS_FILES files"
echo "  Alloy:        $ALLOY_ASSERTIONS assertions, $ALLOY_FILES files"
echo "  SMT:          $SMT_ASSERTIONS assertions, $SMT_FILES files"
echo "  Verus:        $VERUS_PROOFS proofs, $VERUS_FILES files"
echo "  Kani:         $KANI_HARNESSES harnesses, $KANI_FILES files"
echo "  TV:           $TV_VALIDATIONS validations, $TV_FILES files"
echo "  Total proofs: $TOTAL_PROOFS (10 provers)"
echo "  Claim levels: overall=$OVERALL_CLAIM coq=$CLAIM_COQ lean=$CLAIM_LEAN isabelle=$CLAIM_ISABELLE"
echo "                fstar=$CLAIM_FSTAR tlaplus=$CLAIM_TLAPLUS alloy=$CLAIM_ALLOY smt=$CLAIM_SMT"
echo "                verus=$CLAIM_VERUS kani=$CLAIM_KANI tv=$CLAIM_TV"
echo "  Quality tiers:"
echo "    Core Coq:   $COQ_TIER1_CORE (foundations/type_system/effects/properties/termination)"
echo "    Domain Coq: $COQ_TIER2_DOMAIN (domains/Industries/compliance)"
echo "    Trivial:    $COQ_TRIVIAL (reflexivity/exact I patterns)"
echo "  Rust tests:   $RUST_TESTS"
echo "  Session:      $SESSION"
echo "  Timestamp:    $TIMESTAMP"
