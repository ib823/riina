#!/bin/bash
# Keep codespace alive by generating REAL activity
# The issue: GitHub only counts actual terminal INPUT as activity, not output
#
# This script uses multiple techniques:
# 1. Git operations (read-only) - creates filesystem/network activity
# 2. File system access patterns that trigger VS Code's file watcher
# 3. Process activity that registers with the Codespace monitor

echo "========================================"
echo "Keep-alive started at $(date)"
echo "========================================"
echo ""
echo "IMPORTANT: For reliable keep-alive, also do ONE of these:"
echo "  1. Set GitHub Codespaces timeout to 240 min (max) in settings"
echo "  2. Keep VS Code browser tab focused (not minimized)"
echo "  3. Use 'gh codespace ssh' which maintains active connection"
echo ""
echo "This script creates filesystem activity every 60 seconds."
echo "Press Ctrl+C to stop"
echo "---"

COUNTER=0
KEEPALIVE_FILE="/workspaces/proof/.keepalive_timestamp"

while true; do
    sleep 60  # Every 1 minute
    COUNTER=$((COUNTER + 1))

    echo ""
    echo "[$(date '+%H:%M:%S')] Heartbeat #$COUNTER"

    # Technique 1: Touch a file (triggers VS Code file watcher)
    echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$KEEPALIVE_FILE"

    # Technique 2: Git status (filesystem + possible network)
    git status --porcelain > /dev/null 2>&1

    # Technique 3: Read a small file (I/O activity)
    head -1 /workspaces/proof/CLAUDE.md > /dev/null 2>&1

    # Technique 4: Light process spawn (shows as activity)
    ls /workspaces/proof > /dev/null 2>&1

    # Show status every 5 heartbeats
    if [ $((COUNTER % 5)) -eq 0 ]; then
        echo "  [STATUS] Git branch: $(git branch --show-current 2>/dev/null || echo 'unknown')"
        echo "  [STATUS] Disk usage: $(df -h /workspaces | tail -1 | awk '{print $5}')"

        # Check for active Claude processes
        CLAUDE_PROCS=$(pgrep -c -f "claude" 2>/dev/null || echo "0")
        echo "  [STATUS] Claude processes: $CLAUDE_PROCS"

        # Check for Coq compilation
        COQPROC=$(pgrep -a coqc 2>/dev/null | head -1)
        if [ -n "$COQPROC" ]; then
            echo "  [STATUS] Coq compiling: $(echo $COQPROC | awk '{print $NF}')"
        fi
    fi
done
