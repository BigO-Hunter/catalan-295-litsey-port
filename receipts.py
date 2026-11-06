"""Prove the LinkSlope cure preserves every exported declaration TYPE.

Statements are compared TEXTUALLY and exactly: for each `theorem` the text up to `:=` must be
identical, and for each `def` the whole declaration must be identical. Anything the cure adds
is listed separately (additive-only). The pristine side is read from git (`git show HEAD:path`)
so the comparison cannot be fooled by the working tree.

  python3 receipts.py > /tmp/stat_diff.txt
"""
import pathlib, re, subprocess, sys

PATH = "Submission/CatalanMeasure/GenD/Signed/Data/Consts/LinkSlope.lean"
REPO = pathlib.Path(__file__).parent

def decls(text: str) -> dict[str, str]:
    """name -> declaration text, where a theorem's text stops at its `:=` proof."""
    out, lines, i = {}, text.splitlines(), 0
    while i < len(lines):
        m = re.match(r"^(theorem|def|lemma|abbrev)\s+([A-Za-z_][\w']*)", lines[i])
        if not m:
            i += 1
            continue
        kind, name = m.group(1), m.group(2)
        body, n = [], i
        # a declaration ends at the next line that starts a new top-level command
        while n < len(lines) and not (n > i and re.match(r"^(theorem|def|lemma|abbrev|end|namespace|open|set_option|@|/-)", lines[n])):
            body.append(lines[n])
            n += 1
        chunk = "\n".join(body)
        if kind == "theorem":
            chunk = chunk.split(" := ", 1)[0]
        out[name] = chunk.rstrip()
        i = n
    return out

old = decls(subprocess.run(["git", "show", f"HEAD:{PATH}"], capture_output=True, text=True).stdout)
new = decls((REPO / PATH).read_text())

changed = [n for n in old if n in new and old[n] != new[n]]
gone = [n for n in old if n not in new]
added = [n for n in new if n not in old]

print(f"declarations compared: {len(old)} pre, {len(new)} post")
print(f"STATEMENT CHANGED: {len(changed)}")
for n in changed:
    print(f"  !! {n}")
print(f"MISSING (removed): {len(gone)} {gone}")
print(f"ADDED (additive only): {len(added)}")
for n in added:
    print(f"  + {n}")
print(f"VERDICT: {'IDENTICAL' if not changed and not gone else 'BREAK'}")
sys.exit(1 if changed or gone else 0)
