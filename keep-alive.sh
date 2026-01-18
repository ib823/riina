#!/bin/bash
# Keep codespace alive + monitor Coq compilation progress
echo "Keep-alive started at $(date)"
echo "Monitoring pts/0 Claude session (PID 1750)"
echo "Press Ctrl+C to stop"
echo "---"
while true; do
    sleep 120  # Check every 2 minutes
    echo ""
    echo "[$(date '+%H:%M:%S')] === Status ==="
    # Check if the other claude is still running
    if pgrep -f "claude.*pts/0" > /dev/null 2>&1 || ps -p 1750 > /dev/null 2>&1; then
        echo "Claude (pts/0): RUNNING"
        # Show what coq file is being compiled
        COQPROC=$(ps aux | grep "coqc.*\.v" | grep -v grep | awk '{print $NF}')
        if [ -n "$COQPROC" ]; then
            echo "Compiling: $COQPROC"
        fi
    else
        echo "Claude (pts/0): FINISHED or STOPPED"
    fi
    echo "Codespace: ALIVE"
done
