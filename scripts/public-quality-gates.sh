#!/usr/bin/env bash
# ============================================================================
# public-quality-gates.sh
#
# Gold-standard public repo checks for RIINA.
#
# Usage:
#   bash scripts/public-quality-gates.sh
#
# Exit codes:
#   0 - pass
#   1 - fail
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
REPORT_PATH="$REPO_ROOT/reports/public_quality_status.json"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

OVERALL="PASS"

ARTIFACT_STATUS="PASS"
ARTIFACT_DETAIL=""
GITIGNORE_STATUS="PASS"
GITIGNORE_DETAIL=""
DOCS_STATUS="PASS"
DOCS_DETAIL=""
DOC_DRIFT_STATUS="PASS"
DOC_DRIFT_DETAIL=""
LEDGER_STATUS="PASS"
LEDGER_DETAIL=""
HYGIENE_STATUS="PASS"
HYGIENE_DETAIL=""
METRICS_STATUS="PASS"
METRICS_DETAIL=""
VERSION_STATUS="PASS"
VERSION_DETAIL=""

escape_json() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'
}

echo ""
echo "================================================================"
echo "  RIINA PUBLIC QUALITY GATES"
echo "================================================================"

# ---------------------------------------------------------------------------
# 1) No tracked build artifacts
# ---------------------------------------------------------------------------

artifact_hits="$(git ls-files | grep -E '\.aux$|\.glob$|\.vo$|\.vos$|\.vok$|\.lia\.cache$|\.nia\.cache$|\.crashcoqide$' || true)"
artifact_count="$(printf '%s\n' "$artifact_hits" | sed '/^$/d' | wc -l | tr -d ' ')"
if [ "$artifact_count" -gt 0 ]; then
  ARTIFACT_STATUS="FAIL"
  ARTIFACT_DETAIL="tracked_artifacts=$artifact_count"
  OVERALL="FAIL"
else
  ARTIFACT_STATUS="PASS"
  ARTIFACT_DETAIL="tracked_artifacts=0"
fi

# ---------------------------------------------------------------------------
# 2) .gitignore contains critical Coq artifact patterns
# ---------------------------------------------------------------------------

missing_gitignore=0
for pattern in '*.aux' '*.glob' '*.vo' '*.vos' '*.vok' '.lia.cache' '.nia.cache' '*.crashcoqide'; do
  if ! grep -Fq "$pattern" "$REPO_ROOT/.gitignore"; then
    missing_gitignore=$((missing_gitignore + 1))
  fi
done
if [ "$missing_gitignore" -gt 0 ]; then
  GITIGNORE_STATUS="FAIL"
  GITIGNORE_DETAIL="missing_patterns=$missing_gitignore"
  OVERALL="FAIL"
else
  GITIGNORE_STATUS="PASS"
  GITIGNORE_DETAIL="missing_patterns=0"
fi

# ---------------------------------------------------------------------------
# 3) Required public trust docs exist
# ---------------------------------------------------------------------------

missing_docs=0
for f in README.md SECURITY.md AXIOMS.md PROOF_STATUS.md VERSION; do
  if [ ! -f "$REPO_ROOT/$f" ]; then
    missing_docs=$((missing_docs + 1))
  fi
done
if [ "$missing_docs" -gt 0 ]; then
  DOCS_STATUS="FAIL"
  DOCS_DETAIL="missing_docs=$missing_docs"
  OVERALL="FAIL"
else
  DOCS_STATUS="PASS"
  DOCS_DETAIL="missing_docs=0"
fi

# ---------------------------------------------------------------------------
# 3b) Public-doc drift guards (high-visibility active-build claims)
# ---------------------------------------------------------------------------

drift_hits=0
for check in \
  "README.md::policy axiom|1 \\(policy\\)|1 axiom|4 justified axioms|4,885|4885" \
  "docs/UNDERSTANDING_RIINA.md::4 justified axioms|4,885|4885|249 active proof files" \
  "docs/enterprise/COMPLIANCE_GUIDE.md::4,885|4885|4 justified axioms" \
  "docs/enterprise/COMPLIANCE_PACKAGING.md::4 justified axioms"; do
  file="${check%%::*}"
  pattern="${check##*::}"
  if [ -f "$REPO_ROOT/$file" ] && grep -Eq "$pattern" "$REPO_ROOT/$file"; then
    drift_hits=$((drift_hits + 1))
  fi
done

if [ "$drift_hits" -gt 0 ]; then
  DOC_DRIFT_STATUS="FAIL"
  DOC_DRIFT_DETAIL="stale_claim_files=$drift_hits"
  OVERALL="FAIL"
else
  DOC_DRIFT_STATUS="PASS"
  DOC_DRIFT_DETAIL="stale_claim_files=0"
fi

# ---------------------------------------------------------------------------
# 4) Proof ledgers up-to-date
# ---------------------------------------------------------------------------

if bash "$REPO_ROOT/scripts/update-proof-ledger.sh" --check >/dev/null 2>&1; then
  LEDGER_STATUS="PASS"
  LEDGER_DETAIL="ledger_status=up_to_date"
else
  LEDGER_STATUS="FAIL"
  LEDGER_DETAIL="ledger_status=stale"
  OVERALL="FAIL"
fi

# ---------------------------------------------------------------------------
# 5) Active-build proof hygiene from _CoqProject
# ---------------------------------------------------------------------------

COQ_DIR="$REPO_ROOT/02_FORMAL/coq"
COQ_PROJECT="$COQ_DIR/_CoqProject"

active_admitted=0
active_axioms=0
active_assumptions=0
active_qed=0
active_files=0

if [ -f "$COQ_PROJECT" ]; then
  mapfile -t active_coq_files < <(
    awk '
      {
        line=$0;
        sub(/^[ \t]+/, "", line);
        if (line ~ /^[#-]/ || line == "") next;
        split(line, tok, /[ \t]+/);
        if (tok[1] ~ /\.v$/) print tok[1];
      }
    ' "$COQ_PROJECT"
  )

  active_files="${#active_coq_files[@]}"
  for rel in "${active_coq_files[@]}"; do
    path="$COQ_DIR/$rel"
    [ -f "$path" ] || continue
    admitted_hits="$(grep -Ec '^[[:space:]]*Admitted\.' "$path" || true)"
    axiom_hits="$(grep -Ec '^[[:space:]]*Axiom[[:space:]]+' "$path" || true)"
    assumption_hits="$(grep -Ec '^[[:space:]]*Parameter[[:space:]]+val_rel_n_step_up[[:space:]]' "$path" || true)"
    qed_hits="$(grep -c 'Qed\.' "$path" || true)"
    active_admitted=$((active_admitted + admitted_hits))
    active_axioms=$((active_axioms + axiom_hits))
    active_assumptions=$((active_assumptions + assumption_hits))
    active_qed=$((active_qed + qed_hits))
  done
fi

if [ "$active_admitted" -eq 0 ] && [ "$active_axioms" -eq 0 ] && [ "$active_assumptions" -eq 0 ]; then
  HYGIENE_STATUS="PASS"
else
  HYGIENE_STATUS="FAIL"
  OVERALL="FAIL"
fi
HYGIENE_DETAIL="active_files=$active_files qed=$active_qed admitted=$active_admitted axioms=$active_axioms assumptions=$active_assumptions"

# ---------------------------------------------------------------------------
# 6) metrics.json alignment
# ---------------------------------------------------------------------------

metrics_admitted="NA"
metrics_axioms="NA"
metrics_assumptions="NA"
metrics_qed="NA"
metrics_active_files="NA"
metrics_file="$REPO_ROOT/website/public/metrics.json"
if [ -f "$metrics_file" ]; then
  metrics_admitted="$(grep -m1 -E '"admitted"[[:space:]]*:[[:space:]]*[0-9]+' "$metrics_file" | sed -E 's/[^0-9]*([0-9]+).*/\1/' || true)"
  metrics_axioms="$(grep -m1 -E '"axioms"[[:space:]]*:[[:space:]]*[0-9]+' "$metrics_file" | sed -E 's/[^0-9]*([0-9]+).*/\1/' || true)"
  metrics_assumptions="$(grep -m1 -E '"assumptions"[[:space:]]*:[[:space:]]*[0-9]+' "$metrics_file" | sed -E 's/[^0-9]*([0-9]+).*/\1/' || true)"
  metrics_qed="$(python3 -c "import json; print(json.load(open('$metrics_file'))['proofs']['qedActive'])" 2>/dev/null || echo "NA")"
  metrics_active_files="$(python3 -c "import json; print(json.load(open('$metrics_file'))['coq']['filesActive'])" 2>/dev/null || echo "NA")"
fi

if [ "$metrics_admitted" = "$active_admitted" ] \
  && [ "$metrics_axioms" = "$active_axioms" ] \
  && [ "$metrics_assumptions" = "$active_assumptions" ] \
  && [ "$metrics_qed" = "$active_qed" ] \
  && [ "$metrics_active_files" = "$active_files" ]; then
  METRICS_STATUS="PASS"
else
  METRICS_STATUS="FAIL"
  OVERALL="FAIL"
fi
METRICS_DETAIL="metrics_qed=$metrics_qed metrics_active_files=$metrics_active_files metrics_admitted=$metrics_admitted metrics_axioms=$metrics_axioms metrics_assumptions=$metrics_assumptions"

# ---------------------------------------------------------------------------
# 7) VERSION has a matching tag
# ---------------------------------------------------------------------------

version="$(tr -d ' \n' < "$REPO_ROOT/VERSION")"
if git rev-parse -q --verify "refs/tags/v$version" >/dev/null; then
  VERSION_STATUS="PASS"
  VERSION_DETAIL="version=$version tag=v$version"
else
  VERSION_STATUS="FAIL"
  VERSION_DETAIL="version=$version tag=v$version_missing"
  OVERALL="FAIL"
fi

# ---------------------------------------------------------------------------
# Report and exit
# ---------------------------------------------------------------------------

mkdir -p "$REPO_ROOT/reports"
cat > "$REPORT_PATH" <<EOF
{
  "generated_utc": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "artifact_hygiene": { "status": "$ARTIFACT_STATUS", "detail": "$(escape_json "$ARTIFACT_DETAIL")" },
  "gitignore_coverage": { "status": "$GITIGNORE_STATUS", "detail": "$(escape_json "$GITIGNORE_DETAIL")" },
  "required_docs": { "status": "$DOCS_STATUS", "detail": "$(escape_json "$DOCS_DETAIL")" },
  "public_doc_drift": { "status": "$DOC_DRIFT_STATUS", "detail": "$(escape_json "$DOC_DRIFT_DETAIL")" },
  "proof_ledger_freshness": { "status": "$LEDGER_STATUS", "detail": "$(escape_json "$LEDGER_DETAIL")" },
  "active_build_hygiene": { "status": "$HYGIENE_STATUS", "detail": "$(escape_json "$HYGIENE_DETAIL")" },
  "metrics_alignment": { "status": "$METRICS_STATUS", "detail": "$(escape_json "$METRICS_DETAIL")" },
  "version_tag_alignment": { "status": "$VERSION_STATUS", "detail": "$(escape_json "$VERSION_DETAIL")" },
  "overall": "$OVERALL"
}
EOF

echo ""
echo "Artifact hygiene      : $ARTIFACT_STATUS"
echo "Gitignore coverage    : $GITIGNORE_STATUS"
echo "Required docs         : $DOCS_STATUS"
echo "Public doc drift      : $DOC_DRIFT_STATUS"
echo "Proof ledger freshness: $LEDGER_STATUS"
echo "Active-build hygiene  : $HYGIENE_STATUS"
echo "Metrics alignment     : $METRICS_STATUS"
echo "Version/tag alignment : $VERSION_STATUS"
echo "Report                : $REPORT_PATH"

if [ "$OVERALL" = "PASS" ]; then
  echo -e "${GREEN}Public quality gates passed.${NC}"
  exit 0
fi

echo -e "${RED}Public quality gates failed.${NC}"
echo -e "${YELLOW}Review $REPORT_PATH and resolve failures before public sync.${NC}"
exit 1
