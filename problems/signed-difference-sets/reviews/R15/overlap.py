# Overlap of C17's 213 open rows with other (unsettled, exploration) kill lists.
from pathlib import Path
S = Path(__file__).resolve().parents[2]
mine = {l.split()[0] for l in open(Path(__file__).parent / "rows.out")}
def ids(f, pred=lambda p: True):
    out = set()
    p = S / f
    if not p.exists(): return None
    for l in open(p, encoding="utf-8", errors="replace"):
        t = l.split()
        if t and t[0].startswith("N") and pred(t): out.add(t[0])
    return out
for name, f, pred in [("E8 left (91)", "e8_left.txt", lambda t: True),
                      ("E10 none", "e10.out", lambda t: len(t) > 2 and t[2] == "none"),
                      ("E10 any", "e10.out", lambda t: True),
                      ("gauss_chars", "gauss_chars.out", lambda t: True),
                      ("c7_lp", "c7_lp.out", lambda t: True),
                      ("settle-rules.tsv", "settle-rules.tsv", lambda t: True)]:
    x = ids(f, pred)
    print(name, None if x is None else (len(x), len(mine & x)))
x = ids("e10.out", lambda t: len(t) > 2 and t[2] == "none")
print("in E10 none:", sorted(mine & x, key=lambda a: int(a[1:]))[:40])
