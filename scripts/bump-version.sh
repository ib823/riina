#!/usr/bin/env bash
# ============================================================================
# bump-version.sh — Update version in all canonical locations
#
# Usage:
#   bash scripts/bump-version.sh 0.2.0
#
# Updates:
#   1. VERSION
#   2. 03_PROTO/Cargo.toml  (workspace.package.version)
#   3. 05_TOOLING/Cargo.toml (workspace.package.version)
#   4. flake.nix             (version = "X.Y.Z")
#   5. website/package.json  ("version": "X.Y.Z")
#   6. website footer        (RiinaWebsite.jsx)
# ============================================================================

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: bash scripts/bump-version.sh <version>"
    echo "Example: bash scripts/bump-version.sh 0.2.0"
    exit 1
fi

NEW_VERSION="$1"

# Validate semver format
if ! [[ "$NEW_VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "ERROR: Version must be semver (e.g., 0.2.0), got: $NEW_VERSION"
    exit 1
fi

REPO_ROOT="$(git rev-parse --show-toplevel)"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

echo ""
echo "Bumping version to $NEW_VERSION"
echo ""

# 1. VERSION file
echo "$NEW_VERSION" > "$REPO_ROOT/VERSION"
echo -e "${GREEN}[✓] VERSION${NC}"

# 2. 03_PROTO/Cargo.toml
sed -i "s/^version = \"[0-9]*\.[0-9]*\.[0-9]*\"/version = \"$NEW_VERSION\"/" \
    "$REPO_ROOT/03_PROTO/Cargo.toml"
echo -e "${GREEN}[✓] 03_PROTO/Cargo.toml${NC}"

# 3. 05_TOOLING/Cargo.toml
sed -i "s/^version = \"[0-9]*\.[0-9]*\.[0-9]*\"/version = \"$NEW_VERSION\"/" \
    "$REPO_ROOT/05_TOOLING/Cargo.toml"
echo -e "${GREEN}[✓] 05_TOOLING/Cargo.toml${NC}"

# 4. flake.nix
sed -i "s/version = \"[0-9]*\.[0-9]*\.[0-9]*\"/version = \"$NEW_VERSION\"/" \
    "$REPO_ROOT/flake.nix"
echo -e "${GREEN}[✓] flake.nix${NC}"

# 5. website/package.json
sed -i "s/\"version\": \"[0-9]*\.[0-9]*\.[0-9]*\"/\"version\": \"$NEW_VERSION\"/" \
    "$REPO_ROOT/website/package.json"
echo -e "${GREEN}[✓] website/package.json${NC}"

# 6. Website footer version
sed -i "s/RIINA v[0-9]*\.[0-9]*\.[0-9]*/RIINA v$NEW_VERSION/" \
    "$REPO_ROOT/website/src/RiinaWebsite.jsx"
echo -e "${GREEN}[✓] website/src/RiinaWebsite.jsx (footer)${NC}"

# 7. Dockerfile
sed -i "s/LABEL version=\"[0-9]*\.[0-9]*\.[0-9]*\"/LABEL version=\"$NEW_VERSION\"/" \
    "$REPO_ROOT/Dockerfile"
echo -e "${GREEN}[✓] Dockerfile${NC}"

echo ""
echo -e "${GREEN}All files updated to v$NEW_VERSION${NC}"
