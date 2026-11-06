"""Split giant literal-bearing definitions into <=BLOCK-byte block defs joined by small `++` glue.

Handles two shapes present in L0002_left.lean:
  A) def N : Fin m → List Int := tapes m [ <k items, one per line> ]
  B) def N : Fin m → Int := fun i => (raw_ints% [ <k elems, one line> ]).getD i.val d

Nothing but the body changes: the declared type, name, and every literal item are byte-identical.
"""
import re
import sys
from pathlib import Path

BLOCK = 300_000  # target max bytes per block term
THRESHOLD = 262_144

tapes_re = re.compile(r"^def (\w+) : (Fin \d+) → List Int := tapes (\d+) \[$")
getd_re = re.compile(r"^def (\w+) : (Fin \d+) → Int := fun i => \(raw_ints% \[(.*)\]\)\.getD i\.val (\d+)$")
decl_name_re = re.compile(r"^(?:private |protected )?(?:noncomputable )?(?:def|theorem|lemma|abbrev) (\w+)")


def split_items(items, sizes):
    """Greedy packs consecutive items into blocks of <= BLOCK bytes."""
    blocks, cur, cur_sz = [], [], 0
    for it, sz in zip(items, sizes):
        if cur and cur_sz + sz > BLOCK:
            blocks.append(cur)
            cur, cur_sz = [], 0
        cur.append(it)
        cur_sz += sz
    if cur:
        blocks.append(cur)
    return blocks


def main(src: Path, dst: Path):
    text = src.read_text(encoding="utf-8")
    lines = text.split("\n")
    names = set(decl_name_re.findall(text))
    out, report = [], []
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = tapes_re.match(ln)
        if m:
            name, finty, n = m.group(1), m.group(2), int(m.group(3))
            j = i + 1
            items = []
            while j < len(lines) and lines[j].startswith("raw_ints%"):
                items.append(lines[j])
                j += 1
            if j < len(lines) and lines[j].strip() == "]" and len(items) == n:
                span = sum(len(x) + 1 for x in items) + len(ln) + 2
                if span > THRESHOLD:
                    bnames = []
                    for bi, blk in enumerate(split_items(items, [len(x) + 1 for x in items])):
                        bn = f"{name}_p{bi}"
                        assert bn not in names, f"name clash {bn}"
                        bnames.append(bn)
                        out += [f"private def {bn} : List (List Int) :=", "["] + blk + ["]", ""]
                    body = " ++ ".join(bnames) if len(bnames) > 1 else bnames[0]
                    out.append(f"def {name} : {finty} → List Int := tapes {n} ({body})" if len(bnames) > 1
                               else f"def {name} : {finty} → List Int := tapes {n} {body}")
                    report.append((name, span, len(bnames), "tapes"))
                    i = j + 1
                    continue

        m2 = getd_re.match(ln)
        if m2 and len(ln) > THRESHOLD:
            name, finty, elems, dflt = m2.group(1), m2.group(2), m2.group(3), m2.group(4)
            parts = re.split(r",\s*", elems)
            bnames = []
            for bi, blk in enumerate(split_items(parts, [len(x) + 2 for x in parts])):
                bn = f"{name}_p{bi}"
                assert bn not in names, f"name clash {bn}"
                bnames.append(bn)
                out += [f"private def {bn} : List Int := raw_ints% [" + ", ".join(blk) + "]", ""]
            body = " ++ ".join(bnames) if len(bnames) > 1 else bnames[0]
            out.append(f"def {name} : {finty} → Int := fun i => ({body}).getD i.val {dflt}")
            report.append((name, len(ln), len(bnames), "getD"))
            i += 1
            continue

        out.append(ln)
        i += 1

    dst.write_text("\n".join(out), encoding="utf-8")
    print(f"{src.name}: {len(lines)} lines -> {len(out)} lines; {len(report)} splits")
    for name, span, nb, kind in report:
        print(f"  {name:<8} {span:>8}B -> {nb} blocks ({kind})")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
