#!/usr/bin/env bash
# measure_peak.sh — one comparable peak-RSS + wall number per Lean module.
#
#   ./measure_peak.sh Module/A.lean Module/B.lean ...      append rows to peak.csv
#   ./measure_peak.sh -o out.csv A.lean B.lean             explicit CSV
#   ./measure_peak.sh --selftest                           prove the RSS parser works
#
# Runs exactly the command the OOM investigation used (`lake env lean <file>`),
# wrapped in the platform's own time(1):
#   macOS  /usr/bin/time -l  -> "maximum resident set size" in BYTES
#   Linux  /usr/bin/time -v  -> "Maximum resident set size" in KBYTES
# CSV columns: utc,module,wall_s,maxrss_mb,exit
#
# Requires the module's dependencies to be built already (lake env lean does not
# build them); run `lake build` or your chunk's build first.

set -uo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cd "$root" || exit 1
out=peak.csv
tmp=$(mktemp "${TMPDIR:-/tmp}/measure_peak.XXXXXX")
trap 'rm -f "$tmp"' EXIT

if [ "$(uname -s)" = Darwin ]; then time_flags=(-l); else time_flags=(-v); fi

# parse <stats-file> -> "<wall_s> <maxrss_mb>"
parse() {
  awk '
    /maximum resident set size/ {
      for (i = 1; i <= NF; i++) if ($i ~ /^[0-9]+$/) { v = $i; break }
      if (ENVIRON["OS"] == "Darwin") mb = v / 1048576; else mb = v / 1024
    }
    /Maximum resident set size \(kbytes\)/ { mb = $NF / 1024 }
    $2 == "real" { w = $1 }
    /Elapsed \(wall clock\)/ {
      for (i = 1; i <= NF; i++) if ($i ~ /^[0-9:.]+$/ && $i ~ /:/) { split($i, t, ":"); w = t[1]*3600 + t[2]*60 + t[3] }
    }
    END { printf "%.2f %.1f\n", w, mb }
  ' ENVIRON_OS=1 "$1" 2>/dev/null
}

selftest() {
  echo "== selftest: allocating 64 MB under the platform timer =="
  /usr/bin/time "${time_flags[@]}" -o "$tmp" python3 -c 'x = bytearray(64 << 20); print(len(x) // 1048576)' >/dev/null 2>&1
  read -r w mb < <(OS=$(uname -s) parse "$tmp")
  echo "parsed wall=${w}s maxrss=${mb}MB"
  if awk -v m="$mb" 'BEGIN { exit !(m >= 55 && m < 4096) }'; then
    echo "PASS: RSS parser reports a plausible figure"
  else
    echo "FAIL: RSS parser produced '${mb}' — platform time(1) output may differ" >&2
    return 1
  fi
}

if [ "${1:-}" = --selftest ]; then selftest; exit $?; fi
if [ "${1:-}" = -o ]; then out=$2; shift 2; fi
[ $# -gt 0 ] || { echo "usage: $0 [-o out.csv] <Module.lean>..." >&2; exit 2; }
command -v lake >/dev/null || { echo "error: lake not on PATH" >&2; exit 1; }
[ -f "$out" ] || echo "utc,module,wall_s,maxrss_mb,exit" > "$out"

fail=0
for f in "$@"; do
  [ -f "$f" ] || { echo "error: no such file: $f" >&2; fail=1; continue; }
  /usr/bin/time "${time_flags[@]}" -o "$tmp" lake env lean "$f" 2>/dev/null
  rc=$?
  read -r w mb < <(OS=$(uname -s) parse "$tmp")
  printf '%s,%s,%s,%s,%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$f" "${w:-?}" "${mb:-?}" "$rc" >> "$out"
  printf '%-70s wall=%ss peakRSS=%sMB exit=%s\n' "$f" "${w:-?}" "${mb:-?}" "$rc"
  [ "$rc" -eq 0 ] || fail=1
done
echo "rows appended to $out"
exit "$fail"
