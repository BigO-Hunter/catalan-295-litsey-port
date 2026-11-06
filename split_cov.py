"""Split the `covSK` decisions of LinkSlope.lean into per-cell `decide +kernel` slices.

Each `covSK` is one atomic kernel decision over n+1 cells:
  covM1P1 c S cs = zNonnegCov c S (-(2^S)) cs (2^S)
                 = zNonnegCheck c S A c1 && zNonnegCheck c S c1 c2 && ... && zNonnegCheck c S cn B
so the kernel must build *every* cell's Mobius coefficient table inside one term, and the peak
is their sum. Per-cell theorems cut that into n+1 independent kernel runs; the `covSK`
statement is then re-derived with a boolean glue that mentions only the cell checks, never a
coefficient table, so the glue cannot rebuild the giant term.

Usage: python3 split_cov.py [--only 0,1] [--out PATH]
"""
import pathlib, re, sys

REPO = pathlib.Path(__file__).parent
SRC = pathlib.Path(sys.argv[sys.argv.index("--src") + 1]) if "--src" in sys.argv else REPO / "Submission/CatalanMeasure/GenD/Signed/Data/Consts/LinkSlope.lean"
OUT = pathlib.Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else SRC
ONLY = {int(x) for x in sys.argv[sys.argv.index("--only") + 1].split(",")} if "--only" in sys.argv else None

text = SRC.read_text()

cuts = {}
for m in re.finditer(r"^def cutsS(\d+) : List ℤ := raw_ints% \[(.*?)\]", text, re.M):
    cuts.setdefault(int(m.group(1)), [t.strip() for t in m.group(2).split(",") if t.strip()])
for m in re.finditer(r"^def cutsS(\d+) : List ℤ := raw_ints% \[\]", text, re.M):
    cuts[int(m.group(1))] = []

COV = re.compile(r"^theorem (covS(\d+)) : covM1P1 \(slopeN (PnS\2) (\d+)\) (\d+) cutsS\2 = true := by decide \+kernel$")

out, replaced, skipped = [], [], []
for line in text.splitlines():
    m = COV.match(line)
    if not m:
        out.append(line)
        continue
    k = int(m.group(2))
    if ONLY is not None and k not in ONLY:
        out.append(line)
        continue
    cs, S, pn, T, name = cuts[k], m.group(5), m.group(3), m.group(4), m.group(1)
    if not cs:                      # 0 cuts = a single atomic cell check: nothing to split
        skipped.append((name, 0))
        out.append(line)
        continue
    A, B = f"(-(2 : ℤ) ^ {S})", f"(2 ^ {S})"
    endpoints, prev = [], A
    for c in cs:
        endpoints.append((prev, f"({c} : ℤ)"))
        prev = f"({c} : ℤ)"
    endpoints.append((prev, B))
    head = f"zNonnegCheck (slopeN {pn} {T}) {S}"
    names = []
    for i, (a, b) in enumerate(endpoints):
        nm = f"{name}_cell{i}"
        names.append(nm)
        out.append(f"theorem {nm} : {head} {a} {b} = true := by decide +kernel")
    lits = "[" + ", ".join(cs) + "]"
    out.append(f"theorem {name} : covM1P1 (slopeN {pn} {T}) {S} cutsS{k} = true := by")
    out.append(f"  have h : cutsS{k} = ({lits} : List ℤ) := rfl")
    out.append("  rw [h]")
    out.append("  simp only [covM1P1, zNonnegCov, " + ", ".join(names) + ", Bool.and_true]")
    replaced.append((name, len(endpoints)))

OUT.write_text("\n".join(out) + "\n")
print("split:", replaced)
print("uncuttable (0 cuts):", [n for n, _ in skipped])
print("wrote", OUT, OUT.stat().st_size)
