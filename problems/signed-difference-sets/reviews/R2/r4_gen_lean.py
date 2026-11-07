"""Write an independent Lean check of O6-O11: sets as lists of plus/minus elements."""
import sys
from pathlib import Path
ROOT = Path(sys.argv[1]); OUT = Path(sys.argv[2])
CASES = [("N49", "O6", [5, 5], 12, 1), ("N61", "O7", [3, 3, 3], 10, 1), ("N62", "O8", [3, 9], 10, 1),
         ("N67", "O9", [3, 3, 3], 14, 5), ("N68", "O10", [3, 9], 14, 5), ("N73", "O11", [3, 3, 3], 17, 8)]
out = ["import SignedDifferenceSets.Check", "", "/-! Refuter's independent re-check of O6-O11. -/", "",
       "namespace R4Refuter", "open SignedDifferenceSets", ""]
for nid, oid, fs, k, lam in CASES:
    typ = " × ".join("ZMod %d" % f for f in fs)
    plus, minus = [], []
    for ln in (ROOT / "objects" / (oid + ".txt")).read_text(encoding="utf-8").split("\n")[1:]:
        if not ln.strip(): continue
        *c, s = ln.split()
        el = "(" + ", ".join("(%s : ZMod %d)" % (x, f) for x, f in zip(c, fs)) + ")"
        (plus if s == "+" else minus).append(el)
    n = nid.lower()
    out += ["def P%s : List (%s) := [%s]" % (n, typ, ", ".join(plus)),
            "def M%s : List (%s) := [%s]" % (n, typ, ", ".join(minus)),
            "def D%s (x : %s) : SignType := if x ∈ P%s then 1 else if x ∈ M%s then -1 else 0" % (n, typ, n, n),
            "set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
            "theorem has_%s : HasSDS (%s) %d %d := ⟨D%s, by decide⟩" % (n, typ, k, lam, n),
            "#print axioms has_%s" % n, ""]
out += ["end R4Refuter", ""]
OUT.write_text("\n".join(out), encoding="utf-8")
