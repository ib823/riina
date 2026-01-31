#!/usr/bin/env bash
# Install RIINA git hooks into the local repository.
# Usage: ./00_SETUP/scripts/install_hooks.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
HOOKS_SRC="${REPO_ROOT}/00_SETUP/hooks"
HOOKS_DST="${REPO_ROOT}/.git/hooks"

echo "RIINA hook installer"
echo "Repo root: ${REPO_ROOT}"

# Ensure riinac is built
if [ ! -x "${REPO_ROOT}/03_PROTO/target/release/riinac" ] && \
   [ ! -x "${REPO_ROOT}/03_PROTO/target/debug/riinac" ]; then
    echo "Building riinac..."
    (cd "${REPO_ROOT}/03_PROTO" && cargo build -p riinac)
fi

# Install pre-commit hook
if [ -f "${HOOKS_SRC}/pre-commit" ]; then
    cp "${HOOKS_SRC}/pre-commit" "${HOOKS_DST}/pre-commit"
    chmod +x "${HOOKS_DST}/pre-commit"
    echo "Installed: pre-commit  (riinac verify --fast)"
else
    echo "Warning: pre-commit hook source not found"
fi

# Install pre-push hook
if [ -f "${HOOKS_SRC}/pre-push" ]; then
    cp "${HOOKS_SRC}/pre-push" "${HOOKS_DST}/pre-push"
    chmod +x "${HOOKS_DST}/pre-push"
    echo "Installed: pre-push   (riinac verify --full + security checks)"
else
    echo "Warning: pre-push hook source not found"
fi

echo "Done. Hooks installed to ${HOOKS_DST}"
