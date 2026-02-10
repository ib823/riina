#!/usr/bin/env bash
# ============================================================================
# deploy-website.sh — Build website and push to gh-pages on ib823/riina
#
# Usage:
#   bash scripts/deploy-website.sh
#
# Prerequisites:
#   - riina remote configured with push access
#   - Node.js + npm available
#
# This script:
#   1. Builds the website (npm run build in website/)
#   2. Copies install.sh into dist/ (so it's fetchable from GitHub Pages)
#   3. Creates/updates the gh-pages branch on riina remote
#   4. Force-pushes (gh-pages is a deploy branch, not a history branch)
# ============================================================================

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
WEBSITE_DIR="$REPO_ROOT/website"
DIST_DIR="$WEBSITE_DIR/dist"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo ""
echo "================================================================"
echo "  RIINA: DEPLOY WEBSITE → gh-pages"
echo "================================================================"
echo ""

# Step 1: Verify riina remote exists
if ! git remote | grep -q "^riina$"; then
    echo -e "${RED}ERROR: riina remote not configured${NC}"
    echo "Run: git remote add riina https://ib823:<TOKEN>@github.com/ib823/riina.git"
    exit 1
fi
echo -e "${GREEN}[✓] riina remote configured${NC}"

# Step 2: Refresh metrics and enforce public quality/claim gates
echo ""
echo "Refreshing public metrics..."
bash "$REPO_ROOT/scripts/generate-metrics.sh" --fast >/dev/null
echo -e "${GREEN}[✓] metrics.json refreshed${NC}"

echo "Running public quality gates..."
bash "$REPO_ROOT/scripts/public-quality-gates.sh" >/dev/null || {
    echo -e "${RED}ERROR: public quality gates failed (claims/metrics/docs integrity).${NC}"
    echo "Run: bash scripts/public-quality-gates.sh"
    exit 1
}
echo -e "${GREEN}[✓] public quality gates passed${NC}"

if [ "${REQUIRE_ISABELLE:-0}" = "1" ]; then
    if command -v isabelle >/dev/null 2>&1; then
        echo -e "${GREEN}[✓] Isabelle toolchain found (REQUIRE_ISABELLE=1)${NC}"
    else
        echo -e "${RED}ERROR: REQUIRE_ISABELLE=1 but 'isabelle' is not installed.${NC}"
        exit 1
    fi
else
    if ! command -v isabelle >/dev/null 2>&1; then
        echo -e "${YELLOW}WARNING: Isabelle not found (set REQUIRE_ISABELLE=1 to enforce locally).${NC}"
    fi
fi

# Step 3: Build WASM binary for playground
echo ""
echo "Building WASM binary..."
bash "$REPO_ROOT/scripts/build-wasm.sh" || {
    echo -e "${YELLOW}WARNING: WASM build skipped (stub .wasm will be used)${NC}"
}
echo -e "${GREEN}[✓] WASM build step complete${NC}"

# Step 4: Build website
echo ""
echo "Building website..."
(cd "$WEBSITE_DIR" && npm install --silent && npm run build) || {
    echo -e "${RED}ERROR: Website build failed${NC}"; exit 1;
}
echo -e "${GREEN}[✓] Website built${NC}"

# Re-check gates after website prebuild hooks regenerate metrics/assets.
echo "Re-running public quality gates after build..."
bash "$REPO_ROOT/scripts/public-quality-gates.sh" >/dev/null || {
    echo -e "${RED}ERROR: public quality gates failed after build regeneration.${NC}"
    exit 1
}
echo -e "${GREEN}[✓] post-build public quality gates passed${NC}"

# Step 5: Copy install.sh into dist so it's served at /riina/install.sh
cp "$REPO_ROOT/scripts/install.sh" "$DIST_DIR/install.sh"
echo -e "${GREEN}[✓] install.sh copied to dist/${NC}"

# Step 6: Add .nojekyll (GitHub Pages should serve raw files, no Jekyll processing)
touch "$DIST_DIR/.nojekyll"

# Step 7: Create a temporary git repo in dist/ and push to gh-pages
cd "$DIST_DIR"
git init --quiet
git checkout -b gh-pages --quiet
git add -A
git commit -m "Deploy website $(date -u +%Y-%m-%dT%H:%M:%SZ)" --quiet

# Get riina remote URL
RIINA_URL=$(git -C "$REPO_ROOT" remote get-url riina)

echo ""
echo "Pushing to riina/gh-pages..."
git push --force "$RIINA_URL" gh-pages 2>&1 || {
    echo -e "${RED}ERROR: Push to riina failed. Check token permissions.${NC}"
    cd "$REPO_ROOT"
    rm -rf "$DIST_DIR/.git"
    exit 1
}

# Cleanup
cd "$REPO_ROOT"
rm -rf "$DIST_DIR/.git"

echo -e "${GREEN}[✓] Website deployed to gh-pages${NC}"
echo ""
echo "================================================================"
echo -e "  ${GREEN}DEPLOY COMPLETE${NC}"
echo ""
echo "  URL: https://ib823.github.io/riina/"
echo "  Branch: gh-pages on ib823/riina"
echo ""
echo "  If this is the first deploy, enable GitHub Pages:"
echo "    Repository → Settings → Pages → Source: Deploy from branch"
echo "    Branch: gh-pages / (root)"
echo "================================================================"
echo ""
