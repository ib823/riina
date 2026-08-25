#!/usr/bin/env bash
# mirror-propagate-metrics.sh — propagate metrics.json into the docs that quote it.
#
# THIS IS NOT `sync-metrics.sh`.
#
# The upstream pipeline (`sync-public.sh -> sync-metrics.sh -> deploy-website.sh`,
# see .github/copilot-instructions.md) lives on the private tree and does more
# than this: among other things it writes the CLAUDE.md verification banner, and
# CLAUDE.md is not present in this mirror at all. `scripts/sync-metrics.sh` does
# not exist here and never has. Rather than half-reimplement it under its own
# name — two different scripts sharing a path across trees that are supposed to
# be identical is a merge hazard — this covers only the part a mirror actually
# needs, under a name that cannot be confused with it.
#
# What it does: reads website/public/metrics.json (the source of truth, written
# by scripts/generate-metrics.sh) and rewrites the numbers quoted in the
# repository's documentation to match.
#
# What it does NOT do: recompute anything. It never touches metrics.json. Run
# `bash scripts/generate-metrics.sh` first to refresh the numbers themselves.
#
# Usage:
#   bash scripts/mirror-propagate-metrics.sh           # rewrite the docs
#   bash scripts/mirror-propagate-metrics.sh --check    # report drift, exit 1, write nothing
#
# `--check` is the same idiom as generate-sbom.sh --check, so it can be wired
# into CI as a drift gate.
#
# # Why the rewrite is anchored rather than global
#
# The obvious implementation — replace the old count with the new one everywhere
# — is WRONG here, and quietly so. The string "<N> Rust tests" also appears in
# CHANGELOG entries recording what PAST releases measured ("2,294 Rust tests (up
# from 1,282)"), and "<N> Coq Qed" appears in README's competitor comparison
# table. Rewriting those would falsify the historical record. Bare digit
# replacement is worse still: the count has previously collided with substrings
# inside 05_TOOLING's ACVP test-vector files.
#
# So every rewrite is anchored to a line whose *shape* marks it as a live claim:
# the `**Verification:**` banner, and the expected-output line in CONTRIBUTING's
# quickstart. A number in any other context is left alone.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

CHECK=0
case "${1:-}" in
    --check) CHECK=1 ;;
    "") ;;
    *)
        echo "usage: $0 [--check]" >&2
        exit 2
        ;;
esac

METRICS="website/public/metrics.json"
[ -f "$METRICS" ] || {
    echo "ERROR: $METRICS not found — run scripts/generate-metrics.sh first." >&2
    exit 1
}

# A private temp file, cleaned up on any exit path. Not a fixed /tmp name:
# two concurrent runs (a developer and a CI job on the same box) would otherwise
# race on it, and a stale one left by a killed run would be read as input.
FILELIST="$(mktemp "${TMPDIR:-/tmp}/riina-propagate-files.XXXXXX")"
trap 'rm -f "$FILELIST"' EXIT

# Tracked text files only: keeps target/, node_modules/ and .git out without
# needing a prune list, and means an untracked scratch file is never rewritten.
git ls-files -z -- '*.md' '*.txt' > "$FILELIST"

CHECK="$CHECK" METRICS="$METRICS" FILELIST="$FILELIST" python3 - <<'PY'
import json, os, re, sys

check = os.environ["CHECK"] == "1"
metrics_path = os.environ["METRICS"]

try:
    with open(metrics_path, encoding="utf-8") as fh:
        metrics = json.load(fh)
except (OSError, json.JSONDecodeError) as exc:
    sys.exit(f"ERROR: cannot read {metrics_path}: {exc}")

try:
    tests = int(metrics["rust"]["tests"])
    qed = int(metrics["proofs"]["qedActive"])
except (KeyError, TypeError, ValueError) as exc:
    sys.exit(f"ERROR: {metrics_path} is missing a field this script needs: {exc}")

# The banner quotes Qed with thousands separators and the test count bare, which
# is how all 14 current banners are written.
want_tests = str(tests)
want_qed = f"{qed:,}"

# (anchor, pattern-within-the-anchored-line, replacement-builder)
#
# The anchor decides WHICH lines are eligible; the inner pattern decides what
# changes inside them. Both must match or the line is untouched.
RULES = [
    (
        re.compile(r"^\*\*Verification:\*\*"),
        re.compile(r"(?<![\d,])[\d,]+(?= Coq Qed\b)"),
        want_qed,
    ),
    (
        re.compile(r"^\*\*Verification:\*\*"),
        re.compile(r"(?<![\d,])[\d,]+(?= Rust tests\b)"),
        want_tests,
    ),
    (
        re.compile(r"should show [\d,]+ passing"),
        re.compile(r"(?<=should show )[\d,]+(?= passing)"),
        want_tests,
    ),
]

with open(os.environ["FILELIST"], "rb") as fh:
    paths = [p.decode() for p in fh.read().split(b"\0") if p]

stale = []      # (path, lineno, before, after)
changed = set()

for path in paths:
    try:
        with open(path, encoding="utf-8") as fh:
            lines = fh.readlines()
    except (OSError, UnicodeDecodeError):
        continue  # not text we can reason about; leave it alone

    edited = False
    for i, line in enumerate(lines):
        new = line
        for anchor, inner, replacement in RULES:
            if anchor.search(new):
                new = inner.sub(replacement, new)
        if new != line:
            stale.append((path, i + 1, line.rstrip("\n"), new.rstrip("\n")))
            lines[i] = new
            edited = True

    if edited:
        changed.add(path)
        if not check:
            with open(path, "w", encoding="utf-8") as fh:
                fh.writelines(lines)

# Fail closed if the anchors themselves have gone missing. A silent no-op here
# would look identical to "everything is already in sync", which is exactly how
# a propagation step rots: the banner gets reworded, the script stops matching,
# and nobody notices until the published numbers are months stale.
banners = sum(
    1
    for path in paths
    for line in open(path, encoding="utf-8", errors="ignore")
    if line.startswith("**Verification:**")
)
if banners == 0:
    sys.exit(
        "ERROR: no `**Verification:**` banner found in any tracked document.\n"
        "       The anchor this script keys on has changed. Refusing to report\n"
        "       success on a no-op — update the RULES table in this script."
    )

print(f"metrics.json: {tests} Rust tests, {qed:,} Coq Qed")
print(f"banner lines found: {banners}")

if not stale:
    print("docs are in sync; nothing to do.")
    sys.exit(0)

verb = "STALE" if check else "updated"
for path, lineno, before, after in stale:
    print(f"  [{verb}] {path}:{lineno}")
    if check:
        print(f"      - {before.strip()[:120]}")
        print(f"      + {after.strip()[:120]}")

print(f"\n{len(stale)} line(s) across {len(changed)} file(s).")

if check:
    print("\nRun `bash scripts/mirror-propagate-metrics.sh` to fix.", file=sys.stderr)
    sys.exit(1)
PY
