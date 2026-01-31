#!/bin/bash
#═══════════════════════════════════════════════════════════════════════════════════
#  RIINA COMPREHENSIVE INTEGRITY VERIFICATION
#  Run manually for integrity monitoring
#═══════════════════════════════════════════════════════════════════════════════════

set -e

REPO_ROOT="$(git rev-parse --show-toplevel)"
TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)

echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║  RIINA INTEGRITY VERIFICATION REPORT                             ║"
echo "║  Generated: $TIMESTAMP"
echo "╚══════════════════════════════════════════════════════════════════╝"
echo ""

# 1. Git State
echo "=== GIT STATE ==="
echo "Branch:  $(git -C "$REPO_ROOT" branch --show-current)"
echo "HEAD:    $(git -C "$REPO_ROOT" rev-parse HEAD)"
echo "Date:    $(git -C "$REPO_ROOT" log -1 --format=%ci)"
echo "Author:  $(git -C "$REPO_ROOT" log -1 --format='%an <%ae>')"
echo "Sig:     $(git -C "$REPO_ROOT" log -1 --format='%G? %GK' | head -1)"
echo ""

# 2. Signature Verification (last 20 commits)
echo "=== SIGNATURES (last 20) ==="
git -C "$REPO_ROOT" log --pretty=format:"%h %G? %s" -20
echo ""
echo ""

UNSIGNED=$(git -C "$REPO_ROOT" log --pretty=format:"%H %G?" -50 | grep -v " G$" | grep -v " U$" | grep -v " N$" | wc -l)
NOSIG=$(git -C "$REPO_ROOT" log --pretty=format:"%H %G?" -50 | grep " N$" | wc -l)
echo "Unsigned (bad sig): $UNSIGNED in last 50 commits"
echo "No signature:       $NOSIG in last 50 commits"
echo ""

# 3. Repository State Hash
echo "=== REPOSITORY STATE HASH ==="
REPO_HASH=$(find "$REPO_ROOT" -type f \( -name "*.v" -o -name "*.rs" -o -name "*.md" -o -name "*.toml" \) \
    -not -path "*/.git/*" -not -path "*/target/*" \
    -exec sha256sum {} \; | sort | sha256sum | cut -d' ' -f1)
echo "Hash: $REPO_HASH"
echo ""

# 4. Remote comparison
echo "=== REMOTE STATE ==="
git -C "$REPO_ROOT" fetch origin 2>/dev/null || echo "(fetch failed)"
LOCAL_HEAD=$(git -C "$REPO_ROOT" rev-parse HEAD)
REMOTE_HEAD=$(git -C "$REPO_ROOT" rev-parse origin/main 2>/dev/null || echo "UNKNOWN")
echo "Local:  $LOCAL_HEAD"
echo "Remote: $REMOTE_HEAD"
if [ "$LOCAL_HEAD" = "$REMOTE_HEAD" ]; then
    echo "Status: IN SYNC"
else
    echo "Status: DIVERGED"
fi
echo ""

# 5. Admitted/Axiom check
echo "=== PROOF INTEGRITY ==="
ADMITTED_COUNT=$(grep -r "Admitted\." --include="*.v" "$REPO_ROOT/02_FORMAL" 2>/dev/null | grep -v "(\*" | wc -l || echo 0)
AXIOM_COUNT=$(grep -r "^Axiom " --include="*.v" "$REPO_ROOT/02_FORMAL" 2>/dev/null | wc -l || echo 0)
echo "Admitted: $ADMITTED_COUNT"
echo "Axioms:  $AXIOM_COUNT"
echo ""

echo "=== SUMMARY ==="
echo "Timestamp: $TIMESTAMP"
echo "Repo Hash: $REPO_HASH"
echo "Commit:    $(git -C "$REPO_ROOT" rev-parse --short HEAD)"
echo ""
echo "Store this output securely. Compare repo hashes across runs to detect changes."
