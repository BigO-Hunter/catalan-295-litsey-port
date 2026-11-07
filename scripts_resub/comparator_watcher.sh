#!/bin/bash
# Auto-fire the comparator the moment the entry olean exists (build closure done).
# Idempotent: lockfile prevents double-fire; a stop file retires the watcher.
# Log: .w7/comparator_watcher.log   Verdict: .w7/comparator.json
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ENTRY="$ROOT/.lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean"
LOCK="$ROOT/.w7/comparator_watcher.lock"
STOP="$ROOT/.w7/comparator_watcher.stop"
LOG="$ROOT/.w7/comparator_watcher.log"
VERDICT="$ROOT/.w7/comparator.json"

[ -f "$STOP" ] && exit 0
mkdir -p "$ROOT/.w7"
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "[$(date '+%m-%d %H:%M:%S')] another watcher holds the lock — exiting" >> "$LOG"
  exit 0
fi
trap 'rmdir "$LOCK" 2>/dev/null' EXIT
echo "[$(date '+%m-%d %H:%M:%S')] armed; waiting for ${ENTRY#$ROOT/}" >> "$LOG"
while [ ! -f "$ENTRY" ]; do
  [ -f "$STOP" ] && { echo "[$(date '+%m-%d %H:%M:%S')] stopped by stop file" >> "$LOG"; exit 0; }
  sleep 120
done
echo "[$(date '+%m-%d %H:%M:%S')] entry olean present; settling 60s, then firing comparator" >> "$LOG"
sleep 60
if [ -f "$VERDICT" ]; then
  echo "[$(date '+%m-%d %H:%M:%S')] verdict already exists — not refiring" >> "$LOG"
  exit 0
fi
echo "[$(date '+%m-%d %H:%M:%S')] RUN comparator" >> "$LOG"
cd "$ROOT" && python3 scripts_resub/run_comparator.py "$VERDICT" >> "$LOG" 2>&1
echo "[$(date '+%m-%d %H:%M:%S')] comparator done, rc=$? — verdict at $VERDICT" >> "$LOG"
