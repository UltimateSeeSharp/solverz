"""Print header and open/solved docstrings of Erdős Lean files.

Usage: python -I show.py <lean_dir> <number>...
"""
import re
import sys
from pathlib import Path

DOC_CHARS = 450
DECL = re.compile(r"/--((?:(?!-/).)*?)-/\s*@\[([^\]]*)\]\s*(?:theorem|lemma)\s+(\S+)", re.S)

sys.stdout.reconfigure(encoding="utf-8")
lean_dir = Path(sys.argv[1])
for n in sys.argv[2:]:
    t = (lean_dir / f"{n}.lean").read_text(encoding="utf-8")
    h = re.search(r"/-!(.*?)-/", t, re.S)
    print(f"=================== {n}\nHEADER:", " ".join(h[1].split())[:500] if h else "-")
    for m in DECL.finditer(t):
        tag = "OPEN" if "research open" in m[2] else "SOLVED" if "research solved" in m[2] else None
        if tag:
            print(f"[{tag}] {m[3]}: {' '.join(m[1].split())[:DOC_CHARS]}")
