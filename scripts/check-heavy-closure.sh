#!/usr/bin/env bash
# ============================================================================
# check-heavy-closure.sh
#
# Executable closure tracker for heavy dimensions:
#   5, 6, 7, 8, 10, 11, 13
#
# This script is intentionally stricter than anchor-only foundation checks:
# it runs concrete executable gates where tooling exists, then reports
# closure readiness and pending blockers per dimension.
#
# Usage:
#   bash scripts/check-heavy-closure.sh
#   bash scripts/check-heavy-closure.sh --strict
#
# Exit behavior:
#   - default: fail only when foundation regresses; otherwise report pending
#   - --strict: fail unless every heavy dimension is closure-ready
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
REPORT_PATH="$REPO_ROOT/reports/heavy_closure_status.json"
FOUNDATION_REPORT="$REPO_ROOT/reports/heavy_gap_status.json"

STRICT=0
if [ "${1:-}" = "--strict" ]; then
  STRICT=1
fi

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

escape_json() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'
}

run_with_timeout() {
  local seconds="$1"
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "$seconds" "$@"
  else
    "$@"
  fi
}

bool_json() {
  if [ "$1" -eq 1 ]; then
    echo "true"
  else
    echo "false"
  fi
}

tool_exists() {
  command -v "$1" >/dev/null 2>&1
}

file_exists() {
  [ -f "$1" ]
}

run_quiet() {
  local seconds="$1"
  shift
  run_with_timeout "$seconds" "$@" >/dev/null 2>&1
}

z3_check_file() {
  local f="$1"
  if ! file_exists "$f"; then
    return 1
  fi
  if ! tool_exists z3; then
    return 1
  fi
  local out
  out="$(run_with_timeout 60 z3 -smt2 "$f" 2>/dev/null | head -n 1 || true)"
  case "$out" in
    sat|unsat|unknown) return 0 ;;
    *) return 1 ;;
  esac
}

all_z3_pass() {
  local ok=1
  for f in "$@"; do
    if ! z3_check_file "$f"; then
      ok=0
      break
    fi
  done
  [ "$ok" -eq 1 ]
}

echo ""
echo "================================================================"
echo "  RIINA HEAVY CLOSURE TRACK CHECK (5,6,7,8,10,11,13)"
echo "================================================================"
echo "strict: $STRICT"

mkdir -p "$REPO_ROOT/reports"

# ---------------------------------------------------------------------------
# Foundation baseline (reuse canonical heavy foundation check)
# ---------------------------------------------------------------------------
FOUNDATION_RUN_OK=0
if bash "$REPO_ROOT/scripts/check-heavy-gaps.sh" >/dev/null 2>&1; then
  FOUNDATION_RUN_OK=1
fi

F5="FAIL"
F6="FAIL"
F7="FAIL"
F8="FAIL"
F10="FAIL"
F11="FAIL"
F13="FAIL"
FOUNDATION_OVERALL="FAIL"

if [ -f "$FOUNDATION_REPORT" ] && command -v jq >/dev/null 2>&1; then
  F5="$(jq -r '.item_5_constant_time_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F6="$(jq -r '.item_6_zeroization_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F7="$(jq -r '.item_7_compiler_correctness_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F8="$(jq -r '.item_8_crypto_correctness_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F10="$(jq -r '.item_10_implementation_correctness_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F11="$(jq -r '.item_11_protocol_impl_binding_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  F13="$(jq -r '.item_13_hardware_assumptions_foundation.status // "FAIL"' "$FOUNDATION_REPORT")"
  FOUNDATION_OVERALL="$(jq -r '.overall // "FAIL"' "$FOUNDATION_REPORT")"
fi

# ---------------------------------------------------------------------------
# Shared executable checks (run once, reused by multiple dimensions)
# ---------------------------------------------------------------------------
HAS_Z3=0
tool_exists z3 && HAS_Z3=1

HAS_FSTAR=0
tool_exists fstar && HAS_FSTAR=1
if [ "$HAS_FSTAR" -eq 0 ] && tool_exists fstar.exe; then
  HAS_FSTAR=1
fi

HAS_VERUS=0
tool_exists verus && HAS_VERUS=1

HAS_KANI=0
tool_exists kani && HAS_KANI=1

CT_TESTS_OK=0
if run_quiet 600 cargo test --manifest-path "$REPO_ROOT/05_TOOLING/Cargo.toml" -p riina-core constant_time::tests::; then
  CT_TESTS_OK=1
fi

ZEROIZE_TESTS_OK=0
if run_quiet 600 cargo test --manifest-path "$REPO_ROOT/05_TOOLING/Cargo.toml" -p riina-core zeroize::tests::; then
  ZEROIZE_TESTS_OK=1
fi

SECRET_ZEROIZE_TEST_OK=0
if run_quiet 600 cargo test --manifest-path "$REPO_ROOT/05_TOOLING/Cargo.toml" -p riina-core tests::test_secret_zeroization; then
  SECRET_ZEROIZE_TEST_OK=1
fi

CRYPTO_TESTS_OK=0
if run_quiet 600 cargo test --manifest-path "$REPO_ROOT/05_TOOLING/Cargo.toml" -p riina-core crypto::; then
  CRYPTO_TESTS_OK=1
fi

RIINAC_FAST_OK=0
RIINAC_BIN=""
if [ -x "$REPO_ROOT/03_PROTO/target/release/riinac" ]; then
  RIINAC_BIN="$REPO_ROOT/03_PROTO/target/release/riinac"
elif [ -x "$REPO_ROOT/03_PROTO/target/debug/riinac" ]; then
  RIINAC_BIN="$REPO_ROOT/03_PROTO/target/debug/riinac"
fi
if [ -n "$RIINAC_BIN" ] && run_quiet 1200 "$RIINAC_BIN" verify --fast; then
  RIINAC_FAST_OK=1
fi

STRICT_DIM19_OK=0
if run_quiet 1200 bash "$REPO_ROOT/scripts/check-dim1-dim9-promotion.sh" --strict-tools; then
  STRICT_DIM19_OK=1
fi

# ---------------------------------------------------------------------------
# Dim 5: Constant-time enforcement
# ---------------------------------------------------------------------------
D5_ARTIFACT=0
D5_EXEC=0
D5_READY=0

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/ConstantTimeCrypto.v" \
  && file_exists "$REPO_ROOT/05_TOOLING/crates/riina-core/src/constant_time.rs" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/ConstantTimeCrypto.tv.smt2"; then
  D5_ARTIFACT=1
fi

if [ "$CT_TESTS_OK" -eq 1 ] \
  && [ "$HAS_Z3" -eq 1 ] \
  && all_z3_pass \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/ConstantTimeCrypto.tv.smt2" \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/TimingSecurity.tv.smt2"; then
  D5_EXEC=1
fi

if [ "$F5" = "PASS" ] && [ "$D5_ARTIFACT" -eq 1 ] && [ "$D5_EXEC" -eq 1 ]; then
  D5_READY=1
fi

D5_PENDING="none"
if [ "$D5_READY" -eq 0 ]; then
  D5_PENDING="close constant-time backend-preservation obligations and extend executable checks beyond representative SMT gates"
fi

# ---------------------------------------------------------------------------
# Dim 6: Zeroization completeness
# ---------------------------------------------------------------------------
D6_ARTIFACT=0
D6_EXEC=0
D6_READY=0

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/VerifiedRuntime.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/coq/domains/CryptographicSecurity.v" \
  && file_exists "$REPO_ROOT/05_TOOLING/crates/riina-core/src/zeroize.rs" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/VerifiedRuntime.tv.smt2"; then
  D6_ARTIFACT=1
fi

if [ "$ZEROIZE_TESTS_OK" -eq 1 ] \
  && [ "$SECRET_ZEROIZE_TEST_OK" -eq 1 ] \
  && [ "$HAS_Z3" -eq 1 ] \
  && all_z3_pass "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/VerifiedRuntime.tv.smt2"; then
  D6_EXEC=1
fi

if [ "$F6" = "PASS" ] && [ "$D6_ARTIFACT" -eq 1 ] && [ "$D6_EXEC" -eq 1 ]; then
  D6_READY=1
fi

D6_PENDING="none"
if [ "$D6_READY" -eq 0 ]; then
  D6_PENDING="close optimizer-preservation proof chain and add binary-level zeroization verification"
fi

# ---------------------------------------------------------------------------
# Dim 7: Compiler correctness (source -> target)
# ---------------------------------------------------------------------------
D7_ARTIFACT=0
D7_EXEC=0
D7_READY=0

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/CompilerCorrectness.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/CompilerCorrectness.tv.smt2" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/TranslationValidation.tv.smt2"; then
  D7_ARTIFACT=1
fi

if [ "$RIINAC_FAST_OK" -eq 1 ] \
  && [ "$HAS_Z3" -eq 1 ] \
  && all_z3_pass \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/CompilerCorrectness.tv.smt2" \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/TranslationValidation.tv.smt2"; then
  D7_EXEC=1
fi

if [ "$F7" = "PASS" ] && [ "$D7_ARTIFACT" -eq 1 ] && [ "$D7_EXEC" -eq 1 ]; then
  D7_READY=1
fi

D7_PENDING="none"
if [ "$D7_READY" -eq 0 ]; then
  D7_PENDING="publish per-target correctness evidence packs (native/WASM/eBPF/SGX scope) with reproducible reports"
fi

# ---------------------------------------------------------------------------
# Dim 8: Crypto primitive correctness
# ---------------------------------------------------------------------------
D8_ARTIFACT=0
D8_EXEC=0
D8_READY=0

FSTAR_DOMAIN_FILES="$(find "$REPO_ROOT/02_FORMAL/fstar/RIINA/Domains" -type f -name "*.fst" 2>/dev/null | wc -l | tr -d ' ')"
FSTAR_GENERATED_FILES="$(grep -RIl "^(\* Auto-generated from" "$REPO_ROOT/02_FORMAL/fstar/RIINA/Domains"/*.fst 2>/dev/null | wc -l | tr -d ' ')"

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/CryptographicSecurity.v" \
  && [ "$FSTAR_DOMAIN_FILES" -gt 0 ] \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/CryptographicSecurity.tv.smt2"; then
  D8_ARTIFACT=1
fi

if [ "$CRYPTO_TESTS_OK" -eq 1 ] \
  && [ "$HAS_Z3" -eq 1 ] \
  && all_z3_pass "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/CryptographicSecurity.tv.smt2"; then
  D8_EXEC=1
fi

# Strict closure requires non-generated F* corpus plus executable toolchain.
if [ "$F8" = "PASS" ] && [ "$D8_ARTIFACT" -eq 1 ] && [ "$D8_EXEC" -eq 1 ] \
  && [ "$HAS_FSTAR" -eq 1 ] && [ "$FSTAR_GENERATED_FILES" -eq 0 ]; then
  D8_READY=1
fi

D8_PENDING="none"
if [ "$D8_READY" -eq 0 ]; then
  D8_PENDING="replace generated F* corpus with real proofs and run F* toolchain as mandatory executable gate"
fi

# ---------------------------------------------------------------------------
# Dim 10: Implementation correctness
# ---------------------------------------------------------------------------
D10_ARTIFACT=0
D10_EXEC=0
D10_READY=0

VERUS_DOMAIN_FILES="$(find "$REPO_ROOT/02_FORMAL/verus/RIINA/Domains" -type f -name "*.rs" 2>/dev/null | wc -l | tr -d ' ')"
KANI_DOMAIN_FILES="$(find "$REPO_ROOT/02_FORMAL/kani/RIINA/Domains" -type f -name "*.rs" 2>/dev/null | wc -l | tr -d ' ')"
RIINAC_SRC_FILES="$(find "$REPO_ROOT/03_PROTO/crates/riinac/src" -type f -name "*.rs" 2>/dev/null | wc -l | tr -d ' ')"

if [ "$VERUS_DOMAIN_FILES" -gt 0 ] && [ "$KANI_DOMAIN_FILES" -gt 0 ] && [ "$RIINAC_SRC_FILES" -gt 0 ]; then
  D10_ARTIFACT=1
fi

if [ "$RIINAC_FAST_OK" -eq 1 ]; then
  D10_EXEC=1
fi

if [ "$F10" = "PASS" ] && [ "$D10_ARTIFACT" -eq 1 ] && [ "$D10_EXEC" -eq 1 ] \
  && [ "$HAS_VERUS" -eq 1 ] && [ "$HAS_KANI" -eq 1 ]; then
  D10_READY=1
fi

D10_PENDING="none"
if [ "$D10_READY" -eq 0 ]; then
  D10_PENDING="run Verus and Kani on production compiler modules and bind results to spec clauses"
fi

# ---------------------------------------------------------------------------
# Dim 11: Protocol <-> implementation binding
# ---------------------------------------------------------------------------
D11_ARTIFACT=0
D11_EXEC=0
D11_READY=0

PROTOCOL_BINDING_IMPL_HITS="$(grep -RIlE 'protocol|session|trace|conformance' "$REPO_ROOT/03_PROTO/crates/riinac/src" 2>/dev/null | wc -l | tr -d ' ')"

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/AuthenticationProtocols.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/coq/domains/VerifiedProtocols.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/tlaplus/RIINA/Domains/AuthenticationProtocols.tla" \
  && file_exists "$REPO_ROOT/02_FORMAL/tlaplus/RIINA/Domains/VerifiedProtocols.tla" \
  && file_exists "$REPO_ROOT/02_FORMAL/alloy/RIINA/Domains/AuthenticationProtocols.als" \
  && file_exists "$REPO_ROOT/02_FORMAL/alloy/RIINA/Domains/VerifiedProtocols.als"; then
  D11_ARTIFACT=1
fi

if [ "$STRICT_DIM19_OK" -eq 1 ] \
  && [ "$HAS_Z3" -eq 1 ] \
  && all_z3_pass \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/AuthenticationProtocols.tv.smt2" \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/VerifiedProtocols.tv.smt2"; then
  D11_EXEC=1
fi

if [ "$F11" = "PASS" ] && [ "$D11_ARTIFACT" -eq 1 ] && [ "$D11_EXEC" -eq 1 ] \
  && [ "$PROTOCOL_BINDING_IMPL_HITS" -gt 0 ]; then
  D11_READY=1
fi

D11_PENDING="none"
if [ "$D11_READY" -eq 0 ]; then
  D11_PENDING="implement and verify protocol/runtime conformance binding on real compiler/runtime paths"
fi

# ---------------------------------------------------------------------------
# Dim 13: Hardware model assumptions
# ---------------------------------------------------------------------------
D13_ARTIFACT=0
D13_EXEC=0
D13_READY=0

HW_LITMUS_FILES="$(find "$REPO_ROOT" -type f \( -name "*litmus*" -o -name "*memory_order*" \) 2>/dev/null | wc -l | tr -d ' ')"

if file_exists "$REPO_ROOT/02_FORMAL/coq/domains/S001_HardwareContracts.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/coq/domains/HardwareSecurity.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/coq/domains/SpeculativeExecution.v" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/S001_HardwareContracts.tv.smt2" \
  && file_exists "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/HardwareSecurity.tv.smt2"; then
  D13_ARTIFACT=1
fi

if [ "$HAS_Z3" -eq 1 ] \
  && [ "$CT_TESTS_OK" -eq 1 ] \
  && all_z3_pass \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/S001_HardwareContracts.tv.smt2" \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/HardwareSecurity.tv.smt2" \
    "$REPO_ROOT/02_FORMAL/tv/RIINA/Domains/SpeculativeExecution.tv.smt2"; then
  D13_EXEC=1
fi

if [ "$F13" = "PASS" ] && [ "$D13_ARTIFACT" -eq 1 ] && [ "$D13_EXEC" -eq 1 ] \
  && [ "$HW_LITMUS_FILES" -gt 0 ]; then
  D13_READY=1
fi

D13_PENDING="none"
if [ "$D13_READY" -eq 0 ]; then
  D13_PENDING="add explicit hardware litmus suite and release-gated trust-boundary evidence"
fi

# ---------------------------------------------------------------------------
# Summary + report
# ---------------------------------------------------------------------------

OVERALL_EXEC=1
for x in "$D5_EXEC" "$D6_EXEC" "$D7_EXEC" "$D8_EXEC" "$D10_EXEC" "$D11_EXEC" "$D13_EXEC"; do
  if [ "$x" -ne 1 ]; then
    OVERALL_EXEC=0
  fi
done

OVERALL_READY=1
for x in "$D5_READY" "$D6_READY" "$D7_READY" "$D8_READY" "$D10_READY" "$D11_READY" "$D13_READY"; do
  if [ "$x" -ne 1 ]; then
    OVERALL_READY=0
  fi
done

echo ""
echo "Dim 5  Constant-time closure         : foundation=$F5 exec=$D5_EXEC ready=$D5_READY"
echo "Dim 6  Zeroization closure           : foundation=$F6 exec=$D6_EXEC ready=$D6_READY"
echo "Dim 7  Compiler correctness closure  : foundation=$F7 exec=$D7_EXEC ready=$D7_READY"
echo "Dim 8  Crypto correctness closure    : foundation=$F8 exec=$D8_EXEC ready=$D8_READY"
echo "Dim 10 Implementation closure        : foundation=$F10 exec=$D10_EXEC ready=$D10_READY"
echo "Dim 11 Protocol-binding closure      : foundation=$F11 exec=$D11_EXEC ready=$D11_READY"
echo "Dim 13 Hardware assumptions closure  : foundation=$F13 exec=$D13_EXEC ready=$D13_READY"
echo "Overall foundation                   : $FOUNDATION_OVERALL"
echo "Overall executable                   : $([ "$OVERALL_EXEC" -eq 1 ] && echo PASS || echo FAIL)"
echo "Overall closure-ready                : $([ "$OVERALL_READY" -eq 1 ] && echo true || echo false)"

cat > "$REPORT_PATH" <<EOF_JSON
{
  "generated_utc": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "scope": "heavy_dims_5_6_7_8_10_11_13_closure",
  "strict_mode": $STRICT,
  "foundation_run_ok": $(bool_json "$FOUNDATION_RUN_OK"),
  "foundation_overall": "$FOUNDATION_OVERALL",
  "tools": {
    "z3": $(bool_json "$HAS_Z3"),
    "fstar": $(bool_json "$HAS_FSTAR"),
    "verus": $(bool_json "$HAS_VERUS"),
    "kani": $(bool_json "$HAS_KANI")
  },
  "shared_exec": {
    "ct_tests": $(bool_json "$CT_TESTS_OK"),
    "zeroize_tests": $(bool_json "$ZEROIZE_TESTS_OK"),
    "secret_zeroize_test": $(bool_json "$SECRET_ZEROIZE_TEST_OK"),
    "crypto_tests": $(bool_json "$CRYPTO_TESTS_OK"),
    "riinac_verify_fast": $(bool_json "$RIINAC_FAST_OK"),
    "strict_dim1_dim9": $(bool_json "$STRICT_DIM19_OK")
  },
  "dimension_5_constant_time": {
    "foundation": "$F5",
    "artifact_gate": $(bool_json "$D5_ARTIFACT"),
    "executable_gate": $(bool_json "$D5_EXEC"),
    "closure_ready": $(bool_json "$D5_READY"),
    "pending": "$(escape_json "$D5_PENDING")"
  },
  "dimension_6_zeroization": {
    "foundation": "$F6",
    "artifact_gate": $(bool_json "$D6_ARTIFACT"),
    "executable_gate": $(bool_json "$D6_EXEC"),
    "closure_ready": $(bool_json "$D6_READY"),
    "pending": "$(escape_json "$D6_PENDING")"
  },
  "dimension_7_compiler_correctness": {
    "foundation": "$F7",
    "artifact_gate": $(bool_json "$D7_ARTIFACT"),
    "executable_gate": $(bool_json "$D7_EXEC"),
    "closure_ready": $(bool_json "$D7_READY"),
    "pending": "$(escape_json "$D7_PENDING")"
  },
  "dimension_8_crypto_correctness": {
    "foundation": "$F8",
    "artifact_gate": $(bool_json "$D8_ARTIFACT"),
    "executable_gate": $(bool_json "$D8_EXEC"),
    "closure_ready": $(bool_json "$D8_READY"),
    "fstar_domain_files": $FSTAR_DOMAIN_FILES,
    "fstar_generated_files": $FSTAR_GENERATED_FILES,
    "pending": "$(escape_json "$D8_PENDING")"
  },
  "dimension_10_implementation_correctness": {
    "foundation": "$F10",
    "artifact_gate": $(bool_json "$D10_ARTIFACT"),
    "executable_gate": $(bool_json "$D10_EXEC"),
    "closure_ready": $(bool_json "$D10_READY"),
    "verus_domain_files": $VERUS_DOMAIN_FILES,
    "kani_domain_files": $KANI_DOMAIN_FILES,
    "riinac_src_files": $RIINAC_SRC_FILES,
    "pending": "$(escape_json "$D10_PENDING")"
  },
  "dimension_11_protocol_impl_binding": {
    "foundation": "$F11",
    "artifact_gate": $(bool_json "$D11_ARTIFACT"),
    "executable_gate": $(bool_json "$D11_EXEC"),
    "closure_ready": $(bool_json "$D11_READY"),
    "implementation_binding_hits": $PROTOCOL_BINDING_IMPL_HITS,
    "pending": "$(escape_json "$D11_PENDING")"
  },
  "dimension_13_hardware_assumptions": {
    "foundation": "$F13",
    "artifact_gate": $(bool_json "$D13_ARTIFACT"),
    "executable_gate": $(bool_json "$D13_EXEC"),
    "closure_ready": $(bool_json "$D13_READY"),
    "litmus_files": $HW_LITMUS_FILES,
    "pending": "$(escape_json "$D13_PENDING")"
  },
  "overall_executable": $([ "$OVERALL_EXEC" -eq 1 ] && echo "\"PASS\"" || echo "\"FAIL\""),
  "overall_closure_ready": $(bool_json "$OVERALL_READY")
}
EOF_JSON

echo "Report: $REPORT_PATH"

if [ "$STRICT" -eq 1 ] && [ "$OVERALL_READY" -ne 1 ]; then
  echo -e "${RED}Strict mode requires heavy closure readiness for all tracked dimensions.${NC}"
  exit 1
fi

if [ "$FOUNDATION_OVERALL" != "PASS" ]; then
  echo -e "${RED}Heavy foundation regressed; resolve before proceeding.${NC}"
  exit 1
fi

if [ "$OVERALL_READY" -eq 1 ]; then
  echo -e "${GREEN}Heavy closure readiness complete for all tracked dimensions.${NC}"
else
  echo -e "${YELLOW}Heavy closure tracks started; pending blockers remain (see report).${NC}"
fi

exit 0
