#!/usr/bin/env bash
# ============================================================================
# sync-public.sh — Sync validated main commits to public branch
#
# MANDATORY FLOW:
#   1. All work happens on main
#   2. Commit on main (pre-commit: riinac verify --fast)
#   3. Push main (pre-push: riinac verify --full)
#   4. Run this script to sync to public
#
# Usage:
#   bash scripts/sync-public.sh              # Sync latest main commit
#   bash scripts/sync-public.sh <commit>     # Sync specific commit
#   bash scripts/sync-public.sh <from>..<to> # Sync range of commits
#
# This script:
#   - Verifies you are on main and it's clean
#   - Verifies the commit(s) exist on main
#   - Switches to public branch
#   - Cherry-picks the commit(s)
#   - Removes internal files that should not be on public
#   - Amends the cherry-pick to exclude them
#   - Pushes public
#   - Switches back to main
# ============================================================================

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

REPO_ROOT="$(git rev-parse --show-toplevel)"

# Internal files/dirs that must NEVER appear on public
INTERNAL_PATHS=(
    "01_RESEARCH/"
    "06_COORDINATION/"
    "99_ARCHIVE/"
    "claude_ai_output/"
    "dist/"
    "CLAUDE.md"
    "PROGRESS.md"
    "SESSION_LOG.md"
    "REPO_PROTECTION_GUIDE.md"
    "WORKER_B_SPEC_STORE_REL_REWRITE.md"
    "VERIFICATION_MANIFEST.md"
    "axiom_audit_report.txt"
    "riina-website.jsx"
    "02_FORMAL/coq/CLAUDE_*.md"
    "02_FORMAL/coq/DELEGATION_TASKS.md"
    "02_FORMAL/coq/TASK_PROMPTS.md"
    "02_FORMAL/coq/ZERO_AXIOM_ATTACK_PLAN.md"
    "02_FORMAL/coq/AXIOM_ELIMINATION_STRATEGY.md"
    "02_FORMAL/coq/_CoqProject.backup"
    "02_FORMAL/coq/properties/_archive_deprecated/"
    "04_SPECS/business/"
)

echo ""
echo "================================================================"
echo "  RIINA: SYNC MAIN → PUBLIC"
echo "================================================================"
echo ""

# Step 1: Verify we're on main
CURRENT_BRANCH=$(git branch --show-current)
if [ "$CURRENT_BRANCH" != "main" ]; then
    echo -e "${RED}ERROR: Must be on main branch (currently on: $CURRENT_BRANCH)${NC}"
    echo "Run: git checkout main"
    exit 1
fi
echo -e "${GREEN}[✓] On main branch${NC}"

# Step 2: Verify working tree is clean (tolerate auto-generated VERIFICATION_MANIFEST.md)
DIRTY_FILES=$(git diff --name-only HEAD | grep -v "^VERIFICATION_MANIFEST.md$" || true)
if [ -n "$DIRTY_FILES" ]; then
    echo -e "${RED}ERROR: Uncommitted changes on main. Commit or stash first.${NC}"
    echo "$DIRTY_FILES"
    exit 1
fi
# Restore the manifest if it was auto-modified by pre-push hook
git reset HEAD VERIFICATION_MANIFEST.md 2>/dev/null || true
git checkout -- VERIFICATION_MANIFEST.md 2>/dev/null || true
echo -e "${GREEN}[✓] Working tree clean${NC}"

# Step 3: Verify main has been pushed (commits are validated by pre-push hook)
LOCAL_HEAD=$(git rev-parse main)
REMOTE_HEAD=$(git rev-parse origin/main 2>/dev/null || echo "none")
if [ "$LOCAL_HEAD" != "$REMOTE_HEAD" ]; then
    echo -e "${RED}ERROR: main has unpushed commits.${NC}"
    echo "Push main first (pre-push hook will run riinac verify --full):"
    echo "  git push origin main"
    exit 1
fi
echo -e "${GREEN}[✓] main is pushed and validated${NC}"

# Step 4: Determine commit(s) to sync
if [ $# -ge 1 ]; then
    COMMIT_ARG="$1"
else
    COMMIT_ARG="$(git rev-parse HEAD)"
    echo -e "${YELLOW}    Syncing latest main commit: $(git log --oneline -1 HEAD)${NC}"
fi

# Step 5: Switch to public
echo ""
echo "Switching to public branch..."
git checkout public --quiet

# Step 6: Cherry-pick
echo "Cherry-picking from main..."
if [[ "$COMMIT_ARG" == *".."* ]]; then
    # Range
    git cherry-pick "$COMMIT_ARG" --no-commit || true
else
    # Single commit
    git cherry-pick "$COMMIT_ARG" --no-commit || true
fi

# Step 7: Resolve conflicts
# Internal files (matching INTERNAL_PATHS) → git rm
# Public files (README.md, etc.) → accept main's version
CONFLICTED=$(git diff --name-only --diff-filter=U 2>/dev/null || true)
if [ -n "$CONFLICTED" ]; then
    echo -e "${YELLOW}    Resolving conflicts...${NC}"
    echo "$CONFLICTED" | while read -r f; do
        IS_INTERNAL=false
        for pattern in "${INTERNAL_PATHS[@]}"; do
            case "$f" in
                $pattern*) IS_INTERNAL=true; break ;;
            esac
        done
        if $IS_INTERNAL; then
            echo -e "${YELLOW}      Removing internal: $f${NC}"
            git rm -f --quiet "$f" 2>/dev/null || true
        else
            echo -e "${GREEN}      Keeping (accept main): $f${NC}"
            git checkout --theirs "$f" 2>/dev/null || true
            git add "$f" 2>/dev/null || true
        fi
    done
fi

# Step 8: Remove internal files that may have been introduced
echo "Removing internal files from public..."
REMOVED_COUNT=0
for pattern in "${INTERNAL_PATHS[@]}"; do
    # Use git rm with glob support
    if git ls-files "$pattern" 2>/dev/null | grep -q .; then
        git rm -rf --quiet "$pattern" 2>/dev/null || true
        REMOVED_COUNT=$((REMOVED_COUNT + 1))
    fi
    # Also handle untracked files from cherry-pick
    if ls $REPO_ROOT/$pattern 1>/dev/null 2>&1; then
        rm -rf $REPO_ROOT/$pattern 2>/dev/null || true
    fi
done

if [ $REMOVED_COUNT -gt 0 ]; then
    echo -e "${YELLOW}    Removed $REMOVED_COUNT internal path(s) from public${NC}"
fi

# Step 8: Check if there are changes to commit
if git diff --cached --quiet && git diff --quiet; then
    echo -e "${YELLOW}    No new changes for public branch. Skipping.${NC}"
    git cherry-pick --abort 2>/dev/null || true
    git checkout main --quiet
    echo -e "${GREEN}[✓] Back on main${NC}"
    exit 0
fi

# Step 9: Commit on public
ORIGINAL_MSG=$(git log --format=%B -n 1 "$COMMIT_ARG" 2>/dev/null | head -1)
git add -A
# Final cleanup: force-remove any internal files that git add -A may have re-added
for pattern in "${INTERNAL_PATHS[@]}"; do
    git rm -rf --quiet "$pattern" 2>/dev/null || true
done
# Use --no-verify because main was already fully verified by pre-push hook.
# Without this, the pre-commit hook regenerates VERIFICATION_MANIFEST.md
# during the commit, re-introducing an internal file to public.
git commit --no-verify -m "$(cat <<EOF
$ORIGINAL_MSG

Cherry-picked from main ($(echo $COMMIT_ARG | cut -c1-7)).
Internal files excluded.

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
EOF
)" --quiet

echo -e "${GREEN}[✓] Committed on public${NC}"

# Step 10: Push public to origin (ib823/proof) and riina (ib823/riina)
echo "Pushing public..."
git push origin public
echo -e "${GREEN}[✓] Public branch pushed to origin (ib823/proof)${NC}"

# Also push to riina remote (public → main) if configured
if git remote | grep -q "^riina$"; then
    echo "Pushing to riina remote (public → main)..."
    git push riina public:main
    echo -e "${GREEN}[✓] Public branch pushed to riina (ib823/riina)${NC}"
fi

# Step 11: Switch back to main (clean any conflict artifacts first)
git reset --hard HEAD --quiet 2>/dev/null || true
git checkout main --quiet
echo -e "${GREEN}[✓] Back on main${NC}"

echo ""
echo "================================================================"
echo -e "  ${GREEN}SYNC COMPLETE${NC}"
echo "================================================================"
echo ""
