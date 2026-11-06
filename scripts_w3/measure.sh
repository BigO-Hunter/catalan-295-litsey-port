#!/bin/bash
# measure.sh <label> <src.lean> [olean-out]
# Single-threaded Lean typecheck of ONE file; prints wall + peak RSS (macOS /usr/bin/time -l).
set -u
REPO=/Users/dmitri.arkhipov/bigo-campaign/cat-chunk-W3/repo
LABEL="$1"
SRC="$2"
OUT="${3:-/tmp/w3_$LABEL.olean}"
LAKE_PATHS=$(cd "$REPO" && lake env printenv LEAN_PATH)
export LEAN_PATH="$REPO/build_w3:$LAKE_PATHS"
export LEAN_NUM_THREADS=1
cd "$REPO" || exit 1
rm -f "$OUT"
/usr/bin/time -l lean -R archive/CatalanArchive -o "$OUT" "$SRC"
echo "EXIT=$?"
ls -la "$OUT" 2>/dev/null
