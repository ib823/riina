#!/usr/bin/env bash
# ============================================================================
# provision-formal-tools.sh
#
# Deterministically provision formal verification jars used by strict
# Dimension 9 executable checks (TLA+/Alloy).
#
# Installs into:
#   05_TOOLING/tools/formal/
#
# Usage:
#   bash scripts/provision-formal-tools.sh
#
# Optional env overrides:
#   RIINA_FORMAL_TOOLS_DIR
#   RIINA_TLA2TOOLS_VERSION
#   RIINA_TLA2TOOLS_URL
#   RIINA_TLA2TOOLS_SHA256
#   RIINA_ALLOY_VERSION
#   RIINA_ALLOY_URL
#   RIINA_ALLOY_SHA256
#   RIINA_FORMAL_TOOLS_SMOKE=0   # skip post-install smoke checks
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
FORMAL_TOOLS_DIR="${RIINA_FORMAL_TOOLS_DIR:-$REPO_ROOT/05_TOOLING/tools/formal}"

TLA2TOOLS_VERSION="${RIINA_TLA2TOOLS_VERSION:-1.8.0}"
TLA2TOOLS_URL="${RIINA_TLA2TOOLS_URL:-https://github.com/tlaplus/tlaplus/releases/download/v${TLA2TOOLS_VERSION}/tla2tools.jar}"
TLA2TOOLS_SHA256="${RIINA_TLA2TOOLS_SHA256:-b19fd609e8b6ffd639c6f91e8ec9da341f3fcb32385635cfec5bfc548a25f9f9}"
TLA2TOOLS_JAR="$FORMAL_TOOLS_DIR/tla2tools.jar"

ALLOY_VERSION="${RIINA_ALLOY_VERSION:-6.2.0}"
ALLOY_URL="${RIINA_ALLOY_URL:-https://repo1.maven.org/maven2/org/alloytools/org.alloytools.alloy.dist/${ALLOY_VERSION}/org.alloytools.alloy.dist-${ALLOY_VERSION}.jar}"
ALLOY_SHA256="${RIINA_ALLOY_SHA256:-6037cbeee0e8423c1c468447ed10f5fcf2f2743a2ffc39cb1c81f2905c0fdb9d}"
ALLOY_JAR="$FORMAL_TOOLS_DIR/alloy-${ALLOY_VERSION}/lib/app/org.alloytools.alloy.dist.jar"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

sha256_file() {
  local path="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$path" | awk '{print $1}'
    return 0
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$path" | awk '{print $1}'
    return 0
  fi
  if command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$path" | awk '{print $NF}'
    return 0
  fi
  echo -e "${RED}ERROR: no SHA-256 tool found (sha256sum/shasum/openssl).${NC}" >&2
  return 1
}

download_file() {
  local url="$1"
  local out="$2"
  if command -v curl >/dev/null 2>&1; then
    curl -L --fail --silent --show-error "$url" -o "$out"
    return 0
  fi
  if command -v wget >/dev/null 2>&1; then
    wget -qO "$out" "$url"
    return 0
  fi
  echo -e "${RED}ERROR: neither curl nor wget is available for download.${NC}" >&2
  return 1
}

install_artifact() {
  local name="$1"
  local url="$2"
  local expected_sha="$3"
  local dest="$4"
  local dest_dir
  dest_dir="$(dirname "$dest")"
  mkdir -p "$dest_dir"

  if [ -f "$dest" ]; then
    local existing_sha
    existing_sha="$(sha256_file "$dest")"
    if [ "$existing_sha" = "$expected_sha" ]; then
      echo -e "${GREEN}[ok]${NC} $name already present and checksum matches."
      return 0
    fi
    echo -e "${YELLOW}[warn]${NC} $name exists but checksum mismatch; re-downloading."
  fi

  local tmp
  tmp="$(mktemp)"
  download_file "$url" "$tmp"
  local got_sha
  got_sha="$(sha256_file "$tmp")"
  if [ "$got_sha" != "$expected_sha" ]; then
    rm -f "$tmp"
    echo -e "${RED}ERROR: checksum mismatch for $name.${NC}" >&2
    echo "Expected: $expected_sha" >&2
    echo "Got     : $got_sha" >&2
    return 1
  fi

  mv "$tmp" "$dest"
  chmod 0644 "$dest"
  echo -e "${GREEN}[ok]${NC} installed $name -> $dest"
}

run_smoke_checks() {
  if [ "${RIINA_FORMAL_TOOLS_SMOKE:-1}" = "0" ]; then
    echo -e "${YELLOW}[skip]${NC} smoke checks disabled (RIINA_FORMAL_TOOLS_SMOKE=0)."
    return 0
  fi

  if ! command -v java >/dev/null 2>&1; then
    echo -e "${YELLOW}[warn]${NC} java not found; skipping smoke checks."
    return 0
  fi

  local tla_sample="$REPO_ROOT/02_FORMAL/tlaplus/RIINA/Domains/SessionTypes.tla"
  local alloy_sample="$REPO_ROOT/02_FORMAL/alloy/RIINA/Domains/SessionTypes.als"

  if [ -f "$tla_sample" ]; then
    (
      cd "$(dirname "$tla_sample")"
      java -cp "$TLA2TOOLS_JAR" tla2sany.SANY "$(basename "$tla_sample")" >/dev/null 2>&1
    ) || {
      echo -e "${RED}ERROR: TLA2Tools smoke check failed.${NC}" >&2
      return 1
    }
    echo -e "${GREEN}[ok]${NC} TLA2Tools smoke check passed."
  fi

  if [ -f "$alloy_sample" ]; then
    local alloy_class="${ALLOY_CLI_CLASS:-org.alloytools.alloy.core.infra.Alloy}"
    java -cp "$ALLOY_JAR" "$alloy_class" commands "$alloy_sample" >/dev/null 2>&1 || {
      echo -e "${RED}ERROR: Alloy smoke check failed (class=$alloy_class).${NC}" >&2
      return 1
    }
    echo -e "${GREEN}[ok]${NC} Alloy smoke check passed."
  fi
}

echo ""
echo "================================================================"
echo "  RIINA FORMAL TOOL PROVISIONING"
echo "================================================================"
echo "install-dir: $FORMAL_TOOLS_DIR"

install_artifact "tla2tools-${TLA2TOOLS_VERSION}" "$TLA2TOOLS_URL" "$TLA2TOOLS_SHA256" "$TLA2TOOLS_JAR"
install_artifact "alloy-dist-${ALLOY_VERSION}" "$ALLOY_URL" "$ALLOY_SHA256" "$ALLOY_JAR"
run_smoke_checks

echo ""
echo "Provisioned artifacts:"
echo "  TLA2TOOLS_JAR=$TLA2TOOLS_JAR"
echo "  ALLOY_JAR=$ALLOY_JAR"
echo ""
echo -e "${GREEN}Formal tool provisioning complete.${NC}"
