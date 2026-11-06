"""Classify top-level declarations by byte size in a Lean file (no full read into model context)."""
import re
import sys
import json
from pathlib import Path

path = Path(sys.argv[1])
data = path.read_bytes()
lines = data.split(b"\n")
# offsets
offs = [0]
for ln in lines:
    offs.append(offs[-1] + len(ln) + 1)

decl_re = re.compile(
    rb"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    rb"(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|namespace|section|end|open|variable|set_option|axiom|opaque)\b"
)

starts = []
for i, ln in enumerate(lines):
    m = decl_re.match(ln)
    if m:
        starts.append((i, m.group(1).decode()))

decls = []
for idx, (i, kind) in enumerate(starts):
    end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
    size = offs[end] - offs[i]
    head = lines[i][:200].decode("utf-8", "replace")
    decls.append({"line_start": i + 1, "line_end": end, "bytes": size, "kind": kind, "head": head})

decls.sort(key=lambda d: -d["bytes"])
total = len(data)
print(f"FILE {path.name} bytes={total} lines={len(lines)} decls={len(decls)}")
print(f"{'bytes':>9} {'lines':>7} {'kind':<10} head")
for d in decls[:15]:
    nlines = d["line_end"] - d["line_start"] + 1
    print(f"{d['bytes']:>9} {nlines:>7} {d['kind']:<10} {d['head'][:130]}")
print()
print("--- byte histogram (all decls) ---")
buckets = {}
for d in decls:
    b = d["bytes"]
    key = ">1MB" if b > 1 << 20 else f"{b >> 16}00KB"
    buckets[key] = buckets.get(key, 0) + 1
for k in sorted(buckets):
    print(f"{k:>8}: {buckets[k]}")
print()
print("--- total bytes in decls >256KB:", sum(d["bytes"] for d in decls if d["bytes"] > 262144))
print("--- count >256KB:", sum(1 for d in decls if d["bytes"] > 262144))
print("--- count >512KB:", sum(1 for d in decls if d["bytes"] > 524288))
