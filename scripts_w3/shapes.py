"""Structural detail of the top-N giant declarations: line span, prefix shape, inner-item shape."""
import re
import sys
from pathlib import Path

p = Path(sys.argv[1])
lines = p.read_bytes().split(b"\n")

decl_re = re.compile(rb"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|example)\b")
starts = [(i, m.group(1).decode()) for i, ln in enumerate(lines) if (m := decl_re.match(ln))]
offs = [0]
for ln in lines:
    offs.append(offs[-1] + len(ln) + 1)

decls = []
for k, (i, kind) in enumerate(starts):
    end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
    decls.append((offs[end] - offs[i], i, end, kind))

decls.sort(reverse=True)
for size, i, end, kind in decls[:12]:
    first = lines[i][:110].decode("utf-8", "replace")
    tail = lines[end - 1][:80].decode("utf-8", "replace").strip()
    nraw = sum(1 for j in range(i, end) if lines[j].startswith(b"raw_ints%"))
    rawlens = [len(lines[j]) for j in range(i, end) if lines[j].startswith(b"raw_ints%")]
    print(f"\n{size:>9}B  lines {i+1}..{end}  kind={kind}  raw_ints_lines={nraw}")
    print(f"   first: {first}")
    print(f"   last : {tail}")
    if rawlens:
        print(f"   raw lens: min={min(rawlens)} max={max(rawlens)} avg={sum(rawlens)//len(rawlens)}")
