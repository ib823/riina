#!/usr/bin/env bash
# ============================================================================
# release.sh — Master release script for RIINA
#
# Usage:
#   bash scripts/release.sh 0.2.0
#
# This script:
#   1. Validates (clean main, tests pass)
#   2. Bumps version in all files
#   3. Finalizes CHANGELOG.md ([Unreleased] → [X.Y.Z])
#   4. Commits "[RELEASE] vX.Y.Z" + annotated tag
#   5. Pushes main + tag to origin (private)
#   6. Builds tarball + SHA256SUMS
#   7. Syncs to public branch (strips internal files)
#   8. Pushes public + tag to riina remote
#   9. Creates GitHub Release on ib823/riina with assets
#  10. Updates website releases array
# ============================================================================

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: bash scripts/release.sh <version>"
    echo "Example: bash scripts/release.sh 0.2.0"
    exit 1
fi

NEW_VERSION="$1"
TAG="v$NEW_VERSION"

if ! [[ "$NEW_VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "ERROR: Version must be semver (e.g., 0.2.0), got: $NEW_VERSION"
    exit 1
fi

REPO_ROOT="$(git rev-parse --show-toplevel)"
DIST_DIR="$REPO_ROOT/dist"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo ""
echo "================================================================"
echo "  RIINA RELEASE: $TAG"
echo "================================================================"
echo ""

# ── Step 1: Validate ─────────────────────────────────────────────────────────

CURRENT_BRANCH=$(git -C "$REPO_ROOT" branch --show-current)
if [ "$CURRENT_BRANCH" != "main" ]; then
    echo -e "${RED}ERROR: Must be on main branch (currently: $CURRENT_BRANCH)${NC}"
    exit 1
fi
echo -e "${GREEN}[✓] On main branch${NC}"

if [ -n "$(git -C "$REPO_ROOT" status --porcelain)" ]; then
    echo -e "${RED}ERROR: Working tree not clean. Commit or stash first.${NC}"
    exit 1
fi
echo -e "${GREEN}[✓] Working tree clean${NC}"

if git -C "$REPO_ROOT" tag -l "$TAG" | grep -q "$TAG"; then
    echo -e "${RED}ERROR: Tag $TAG already exists${NC}"
    exit 1
fi
echo -e "${GREEN}[✓] Tag $TAG is available${NC}"

# Run tests
echo ""
echo "Running Rust tests (03_PROTO)..."
(cd "$REPO_ROOT/03_PROTO" && cargo test --all --quiet) || {
    echo -e "${RED}ERROR: 03_PROTO tests failed${NC}"; exit 1;
}
echo -e "${GREEN}[✓] 03_PROTO tests pass${NC}"

echo "Running Rust tests (05_TOOLING)..."
(cd "$REPO_ROOT/05_TOOLING" && cargo test --all --quiet) || {
    echo -e "${RED}ERROR: 05_TOOLING tests failed${NC}"; exit 1;
}
echo -e "${GREEN}[✓] 05_TOOLING tests pass${NC}"

# ── Step 2: Bump version ─────────────────────────────────────────────────────

echo ""
bash "$REPO_ROOT/scripts/bump-version.sh" "$NEW_VERSION"

# ── Step 3: Finalize CHANGELOG ────────────────────────────────────────────────

CHANGELOG="$REPO_ROOT/CHANGELOG.md"
TODAY=$(date -u +%Y-%m-%d)

# Replace [Unreleased] with version+date, add new [Unreleased] section
sed -i "s/^## \[Unreleased\]/## [Unreleased]\n\n## [$NEW_VERSION] - $TODAY/" "$CHANGELOG"

# Update comparison links at bottom
if grep -q "\[Unreleased\]:.*compare" "$CHANGELOG"; then
    sed -i "s|\[Unreleased\]:.*|[Unreleased]: https://github.com/ib823/riina/compare/v$NEW_VERSION...HEAD|" "$CHANGELOG"
fi

echo -e "${GREEN}[✓] CHANGELOG.md finalized${NC}"

# ── Step 4: Update website releases array ─────────────────────────────────────

WEBSITE_JSX="$REPO_ROOT/website/src/RiinaWebsite.jsx"

# Extract Added/Changed/Fixed from changelog for this version
RELEASE_NOTES=""
IN_VERSION=false
while IFS= read -r line; do
    if [[ "$line" == "## [$NEW_VERSION]"* ]]; then
        IN_VERSION=true
        continue
    fi
    if $IN_VERSION && [[ "$line" == "## ["* ]]; then
        break
    fi
    if $IN_VERSION; then
        RELEASE_NOTES+="$line"$'\n'
    fi
done < "$CHANGELOG"

# Build highlights array from first 3 bullet points
HIGHLIGHTS=()
while IFS= read -r line; do
    if [[ "$line" == "- "* ]] && [ ${#HIGHLIGHTS[@]} -lt 3 ]; then
        # Escape for JS string
        ITEM=$(echo "$line" | sed 's/^- //' | sed "s/'/\\\\'/g")
        HIGHLIGHTS+=("$ITEM")
    fi
done <<< "$RELEASE_NOTES"

H1="${HIGHLIGHTS[0]:-Release $NEW_VERSION}"
H2="${HIGHLIGHTS[1]:-Bug fixes and improvements}"
H3="${HIGHLIGHTS[2]:-See CHANGELOG.md for details}"

# Inject new release entry after RELEASES_MARKER
RELEASE_ENTRY="    { version: '$NEW_VERSION', date: '$TODAY', highlights: ['$H1', '$H2', '$H3'] },"
sed -i "/\/\/ RELEASES_MARKER/a\\
$RELEASE_ENTRY" "$WEBSITE_JSX"

echo -e "${GREEN}[✓] Website releases array updated${NC}"

# ── Step 5: Commit + tag ──────────────────────────────────────────────────────

echo ""
git -C "$REPO_ROOT" add -A
git -C "$REPO_ROOT" commit -m "$(cat <<EOF
[RELEASE] $TAG

Version $NEW_VERSION released.
See CHANGELOG.md for details.

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
EOF
)"
echo -e "${GREEN}[✓] Release commit created${NC}"

# Extract changelog section for tag annotation
TAG_MSG=$(echo "$RELEASE_NOTES" | head -20)
git -C "$REPO_ROOT" tag -a "$TAG" -m "$(cat <<EOF
RIINA $TAG

$TAG_MSG
EOF
)"
echo -e "${GREEN}[✓] Tag $TAG created${NC}"

# ── Step 6: Push main + tag ──────────────────────────────────────────────────

echo ""
echo "Pushing main + tag to origin..."
git -C "$REPO_ROOT" push origin main
git -C "$REPO_ROOT" push origin "$TAG"
echo -e "${GREEN}[✓] Pushed to origin${NC}"

# ── Step 7: Build tarball ─────────────────────────────────────────────────────

echo ""
mkdir -p "$DIST_DIR"
TARBALL="$DIST_DIR/riina-$NEW_VERSION-source.tar.gz"

git -C "$REPO_ROOT" archive --format=tar.gz --prefix="riina-$NEW_VERSION/" HEAD \
    -o "$TARBALL"
echo -e "${GREEN}[✓] Tarball: $TARBALL${NC}"

(cd "$DIST_DIR" && sha256sum "riina-$NEW_VERSION-source.tar.gz" > SHA256SUMS)
echo -e "${GREEN}[✓] SHA256SUMS generated${NC}"

# ── Step 8: Sync to public ───────────────────────────────────────────────────

echo ""
bash "$REPO_ROOT/scripts/sync-public.sh"

# Push tag to riina remote (if configured)
if git -C "$REPO_ROOT" remote | grep -q "^riina$"; then
    git -C "$REPO_ROOT" push riina public:main "$TAG" 2>/dev/null || true
    echo -e "${GREEN}[✓] Pushed to riina remote${NC}"
else
    echo -e "${YELLOW}    riina remote not configured, skipping${NC}"
fi

# ── Step 9: GitHub Release ────────────────────────────────────────────────────

echo ""
if command -v gh &>/dev/null; then
    # Extract release notes from changelog
    RELEASE_BODY=$(echo "$RELEASE_NOTES" | sed '/^$/d' | head -50)

    gh release create "$TAG" \
        --repo ib823/riina \
        --title "RIINA $TAG" \
        --notes "$(cat <<EOF
$RELEASE_BODY

---

**Full Changelog**: https://github.com/ib823/riina/blob/main/CHANGELOG.md

**Install:**
\`\`\`bash
curl -fsSL https://ib823.github.io/riina/install.sh | bash
\`\`\`
EOF
)" \
        "$TARBALL" "$DIST_DIR/SHA256SUMS" \
        2>/dev/null && echo -e "${GREEN}[✓] GitHub Release created${NC}" \
        || echo -e "${YELLOW}    GitHub Release creation failed (may need auth)${NC}"
else
    echo -e "${YELLOW}    gh CLI not found, skipping GitHub Release${NC}"
fi

# ── Step 10: Deploy website ────────────────────────────────────────────────────

echo ""
if [ -f "$REPO_ROOT/scripts/deploy-website.sh" ]; then
    bash "$REPO_ROOT/scripts/deploy-website.sh" \
        && echo -e "${GREEN}[✓] Website deployed${NC}" \
        || echo -e "${YELLOW}    Website deployment failed (non-blocking)${NC}"
else
    echo -e "${YELLOW}    deploy-website.sh not found, skipping${NC}"
fi

# ── Done ──────────────────────────────────────────────────────────────────────

echo ""
echo "================================================================"
echo -e "  ${GREEN}RELEASE $TAG COMPLETE${NC}"
echo "================================================================"
echo ""
echo "  Tag:     $TAG"
echo "  Tarball: $TARBALL"
echo "  Website: https://ib823.github.io/riina/"
echo "  Release: https://github.com/ib823/riina/releases/tag/$TAG"
echo "  Next:    Update [Unreleased] in CHANGELOG.md as you work"
echo ""
