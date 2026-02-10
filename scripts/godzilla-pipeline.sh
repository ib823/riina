#!/usr/bin/env bash
# ============================================================================
# godzilla-pipeline.sh — Unified strict RIINA pipeline
#
# Purpose:
#   Chain existing strict scripts in the correct order without redundant calls.
#
# Modes:
#   audit   : full local verification + docs/metrics sync (default)
#   deploy  : audit + sync public + deploy website
#   release : audit + release pipeline (version required)
#
# Usage:
#   bash scripts/godzilla-pipeline.sh
#   bash scripts/godzilla-pipeline.sh audit --deep-level 4
#   bash scripts/godzilla-pipeline.sh deploy --deep-level 4
#   bash scripts/godzilla-pipeline.sh release --version 0.2.0 --deep-level 4
#
# Notes:
#   - This script intentionally reuses existing scripts:
#     generate-metrics.sh, sync-metrics.sh, audit-docs.sh, release.sh,
#     sync-public.sh, deploy-website.sh, security-gates.sh,
#     05_TOOLING/tools/verify_integrity.sh,
#     and 05_TOOLING/scripts/verify.sh.
#   - sync-public.sh already runs verify-public.sh, so this script does not call
#     verify-public.sh directly (avoids redundant execution).
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
MODE="${1:-audit}"
shift || true

DEEP_LEVEL=4
VERSION=""
SYNC_MODE="apply"   # apply|dry
SKIP_DEEP=0

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

usage() {
  cat <<'EOF'
Usage:
  bash scripts/godzilla-pipeline.sh [MODE] [OPTIONS]

MODE:
  audit    Run strict local checks (default)
  deploy   Run audit, then sync public and deploy website
  release  Run audit, then release.sh --version <semver>

OPTIONS:
  --deep-level N      Verification level for 05_TOOLING/scripts/verify.sh (0..6, default: 4)
  --version X.Y.Z     Required for release mode
  --sync dry|apply    sync-metrics mode (default: apply)
  --skip-deep         Skip 05_TOOLING/scripts/verify.sh
  -h, --help          Show this help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --deep-level)
      DEEP_LEVEL="${2:-}"
      shift 2
      ;;
    --version)
      VERSION="${2:-}"
      shift 2
      ;;
    --sync)
      SYNC_MODE="${2:-}"
      shift 2
      ;;
    --skip-deep)
      SKIP_DEEP=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo -e "${RED}Unknown argument: $1${NC}"
      usage
      exit 1
      ;;
  esac
done

if [[ ! "$MODE" =~ ^(audit|deploy|release)$ ]]; then
  echo -e "${RED}Invalid mode: $MODE${NC}"
  usage
  exit 1
fi

if [[ ! "$DEEP_LEVEL" =~ ^[0-6]$ ]]; then
  echo -e "${RED}--deep-level must be 0..6 (got: $DEEP_LEVEL)${NC}"
  exit 1
fi

if [[ ! "$SYNC_MODE" =~ ^(dry|apply)$ ]]; then
  echo -e "${RED}--sync must be dry|apply (got: $SYNC_MODE)${NC}"
  exit 1
fi

if [ "$MODE" = "release" ] && [ -z "$VERSION" ]; then
  echo -e "${RED}release mode requires --version X.Y.Z${NC}"
  exit 1
fi

riinac_bin() {
  if [ -x "$REPO_ROOT/03_PROTO/target/release/riinac" ]; then
    echo "$REPO_ROOT/03_PROTO/target/release/riinac"
    return 0
  fi
  if [ -x "$REPO_ROOT/03_PROTO/target/debug/riinac" ]; then
    echo "$REPO_ROOT/03_PROTO/target/debug/riinac"
    return 0
  fi
  return 1
}

run_step() {
  local msg="$1"
  shift
  echo ""
  echo "================================================================"
  echo "  $msg"
  echo "================================================================"
  "$@"
}

restore_deploy_generated_state() {
  # Audit/deep checks intentionally regenerate local metrics/reports.
  # Deploy must sync committed history only, so restore generated artifacts.
  local paths=(
    "$REPO_ROOT/website/public/metrics.json"
    "$REPO_ROOT/reports/easier_gap_status.json"
    "$REPO_ROOT/reports/medium_gap_status.json"
    "$REPO_ROOT/reports/heavy_gap_status.json"
    "$REPO_ROOT/reports/public_quality_status.json"
    "$REPO_ROOT/VERIFICATION_MANIFEST.md"
  )

  git restore --staged --worktree -- "${paths[@]}" >/dev/null 2>&1 || true
}

ensure_clean_worktree() {
  local context="${1:-operation}"
  if ! git diff --quiet || ! git diff --cached --quiet; then
    echo -e "${RED}ERROR: Working tree is not clean before ${context}.${NC}"
    git status --short
    return 1
  fi
}

run_audit_pipeline() {
  local riinac=""

  run_step "METRICS GENERATION" bash "$REPO_ROOT/scripts/generate-metrics.sh" --fast

  if [ "$SYNC_MODE" = "dry" ]; then
    run_step "METRICS DOC SYNC (DRY RUN)" bash "$REPO_ROOT/scripts/sync-metrics.sh" --dry-run
  else
    run_step "METRICS DOC SYNC (APPLY)" bash "$REPO_ROOT/scripts/sync-metrics.sh"
  fi

  run_step "DOC AUDIT" bash "$REPO_ROOT/scripts/audit-docs.sh"

  if ! riinac="$(riinac_bin)"; then
    run_step "BUILD RIINAC" bash -lc "cd \"$REPO_ROOT/03_PROTO\" && cargo build --release -p riinac"
    riinac="$(riinac_bin)"
  fi

  run_step "RIINAC VERIFY --FULL" "$riinac" verify --full
  run_step "SECURITY GATES" bash "$REPO_ROOT/scripts/security-gates.sh"
  if [ -f "$REPO_ROOT/scripts/check-easier-gaps.sh" ]; then
    run_step "EASIER GAP CLOSURE (1,2,9,12)" bash "$REPO_ROOT/scripts/check-easier-gaps.sh"
  else
    echo -e "${YELLOW}Skipping easier-gap closure check: scripts/check-easier-gaps.sh not found${NC}"
  fi
  if [ -f "$REPO_ROOT/scripts/public-quality-gates.sh" ]; then
    run_step "PUBLIC QUALITY GATES" bash "$REPO_ROOT/scripts/public-quality-gates.sh"
  else
    echo -e "${YELLOW}Skipping public quality gates: scripts/public-quality-gates.sh not found${NC}"
  fi

  if [ "$SKIP_DEEP" -eq 0 ]; then
    if [ -f "$REPO_ROOT/05_TOOLING/scripts/verify.sh" ]; then
      run_step "DEEP VERIFY LEVEL $DEEP_LEVEL" bash "$REPO_ROOT/05_TOOLING/scripts/verify.sh" "$DEEP_LEVEL"
    else
      echo -e "${YELLOW}Skipping deep verify: 05_TOOLING/scripts/verify.sh not found${NC}"
    fi
  else
    echo -e "${YELLOW}Skipping deep verify (--skip-deep)${NC}"
  fi

  if [ -f "$REPO_ROOT/05_TOOLING/tools/verify_integrity.sh" ]; then
    run_step "INTEGRITY VERIFICATION" bash "$REPO_ROOT/05_TOOLING/tools/verify_integrity.sh"
  else
    echo -e "${YELLOW}Skipping integrity verify: 05_TOOLING/tools/verify_integrity.sh not found${NC}"
  fi
}

echo ""
echo "================================================================"
echo "  RIINA GODZILLA PIPELINE ($MODE)"
echo "================================================================"
echo "repo: $REPO_ROOT"
echo "deep-level: $DEEP_LEVEL"
echo "sync-mode: $SYNC_MODE"
echo ""

case "$MODE" in
  audit)
    run_audit_pipeline
    ;;
  deploy)
    if [ "$SYNC_MODE" = "apply" ]; then
      echo -e "${YELLOW}Deploy mode forcing --sync dry to avoid dirty tree before sync-public${NC}"
      SYNC_MODE="dry"
    fi
    run_audit_pipeline
    restore_deploy_generated_state
    ensure_clean_worktree "SYNC PUBLIC"
    run_step "SYNC PUBLIC" bash "$REPO_ROOT/scripts/sync-public.sh"
    run_step "DEPLOY WEBSITE" bash "$REPO_ROOT/scripts/deploy-website.sh"
    if [ -f "$REPO_ROOT/scripts/verify-riina-deploy.sh" ]; then
      run_step "VERIFY /riina END-STATE" bash "$REPO_ROOT/scripts/verify-riina-deploy.sh"
    else
      echo -e "${YELLOW}Skipping /riina deploy verification: script not found${NC}"
    fi
    ;;
  release)
    run_audit_pipeline
    run_step "RELEASE $VERSION" bash "$REPO_ROOT/scripts/release.sh" "$VERSION"
    ;;
esac

echo ""
echo "================================================================"
echo -e "  ${GREEN}GODZILLA PIPELINE COMPLETE (${MODE})${NC}"
echo "================================================================"
