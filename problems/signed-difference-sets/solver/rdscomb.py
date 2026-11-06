"""I15's sets: signed combinations αG + βN + γR of a relative difference set R (ideator round 2, B4).

`rdscomb.py <first object number> [<order-64 sets file>]`: builds each set of ROWS, checks its weight
and every shift's signed count here (independently of the ideator's numpy), and writes
objects/O<id>.txt, one per row. Standard library only. Families (N the forbidden subgroup, R ∩ N = {0}
or ∅):
- F1 = R − N, F1′ = G − R − N with −1 at 0, R semiregular (n², n, n², n): R = {(x + pxy, y)} in
  ℤ_{p²} × ℤ_p (N = ⟨(p, 0)⟩) or {(x, y, xy)} in ℤ_p³ (N = {(0, 0, z)}); order 64: R from the file.
- F3 = G − 2R − N, F4 = G − R − 2N, R Bose's affine RDS {e : Tr(gᵉ) = 1} of GF(q²)* projected to
  ℤ_{n(q+1)} and translated off N.
"""
import ast
import csv
import itertools
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

# (instance, family, construction): "mixed"/"elem" with p, "file" with the row's tag, "bose" with (p, m, n).
ROWS = [
    ("N3243", "F1", ("mixed", 5)), ("N31721", "F1", ("elem", 7)), ("N31722", "F1", ("mixed", 7)),
    ("N3314", "F1p", ("elem", 5)), ("N3315", "F1p", ("mixed", 5)),
    ("N32087", "F1p", ("elem", 7)), ("N32088", "F1p", ("mixed", 7)),
    ("N658", "F1", ("file",)), ("N659", "F1", ("file",)), ("N660", "F1", ("file",)),
    ("N661", "F1", ("file",)), ("N663", "F1", ("file",)), ("N665", "F1", ("file",)),
    ("N736", "F1p", ("file",)), ("N737", "F1p", ("file",)), ("N740", "F1p", ("file",)),
    ("N742", "F1p", ("file",)),
    ("N26075", "F3", ("bose", 5, 4, 12)), ("N47314", "F4", ("bose", 3, 8, 5)),
    # `exists` in the table on Gordon's orbit exhaust, whose stored sets fail the check.
    ("N1134", "F4", ("bose", 5, 4, 3)), ("N9807", "F4", ("bose", 7, 4, 4)),
]


def keys():
    return {r["id"]: r["key"] for r in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8"))}


def semiregular(kind, p):
    """R and N in the instance's coordinate order ([p, p²] or [p, p, p])."""
    if kind == "mixed":
        R = {(y, (x + p * x * y) % (p * p)) for x in range(p) for y in range(p)}
        N = {(0, p * j) for j in range(p)}
    else:
        R = {(x, y, x * y % p) for x in range(p) for y in range(p)}
        N = {(0, 0, z) for z in range(p)}
    return R, N


def from_file(path, shape, family):
    for line in open(path, encoding="utf-8"):
        fac = ast.literal_eval(line[: line.index("]") + 1])
        if fac == shape and line.split()[len(fac)] == family:
            plus = ast.literal_eval(re.search(r"plus=(\[.*?\])", line).group(1))
            minus = ast.literal_eval(re.search(r"minus=(\[.*?\])", line).group(1))
            return {tuple(g): 1 for g in plus} | {tuple(g): -1 for g in minus}
    sys.exit(f"no {family} set for {shape} in {path}")


def gf_log(p, m):
    """Powers of a primitive element x of GF(p^m) = F_p[x]/(f), as coefficient tuples."""
    Q = p ** m
    for red in itertools.product(range(p), repeat=m):
        if red[0] == 0:
            continue
        cur, seen, elems = (1,) + (0,) * (m - 1), set(), []
        for _ in range(Q - 1):
            if cur in seen:
                break
            seen.add(cur)
            elems.append(cur)
            top = cur[-1]
            cur = tuple((c + top * r) % p for c, r in zip((0,) + cur[:-1], red))
        if len(elems) == Q - 1 and cur == elems[0]:
            return elems
    raise ValueError("no primitive polynomial")


def bose(p, m, n):
    """Bose's affine RDS projected to ℤ_{n(q+1)}, translated off N; returns R, N, v."""
    elems = gf_log(p, m)
    Q = p ** m
    q = math.isqrt(Q)
    one = elems[0]
    R0 = [e for e in range(Q - 1)
          if tuple((a + b) % p for a, b in zip(elems[e], elems[e * q % (Q - 1)])) == one]
    v = n * (q + 1)
    N = {(q + 1) * j % v for j in range(n)}
    for t in range(v):
        R = [(e + t) % v for e in R0]
        if len(set(R)) == len(R) and not set(R) & N:
            return {(x,) for x in R}, {(x,) for x in N}, v
    raise ValueError("no translate off N")


def combine(shape, R, N, family):
    G = list(itertools.product(*[range(m) for m in shape]))
    zero = (0,) * len(shape)
    R, N = set(R), set(N)
    coef = {"F1": (0, -1, 1), "F1p": (1, -1, -1), "F3": (1, -1, -2), "F4": (1, -2, -1)}[family]
    a, b, c = coef
    D = {g: a + b * (g in N) + c * (g in R) for g in G}
    if family == "F1p":
        D[zero] = -1
    return {g: x for g, x in D.items() if x}


def check(shape, D, k, lam):
    assert set(D.values()) <= {1, -1}, "values outside {−1, 0, 1}"
    assert len(D) == k, f"weight {len(D)} ≠ {k}"
    G = list(itertools.product(*[range(m) for m in shape]))
    items = list(D.items())
    for g in G[1:]:
        t = sum(x * D.get(tuple((a + b) % m for a, b, m in zip(h, g, shape)), 0) for h, x in items)
        assert t == lam, f"shift {g}: {t} ≠ {lam}"


def main(first, sets_file=None):
    ks = keys()
    for i, (nid, family, cons) in enumerate(ROWS):
        mm = KEY.fullmatch(ks[nid])
        v, k, lam = map(int, mm.groups()[:3])
        shape = [int(x) for x in mm.group(4).split(",")]
        if cons[0] in ("mixed", "elem"):
            D = combine(shape, *semiregular(cons[0], cons[1]), family)
        elif cons[0] == "file":
            D = from_file(sets_file, shape, family)
        else:
            R, N, vv = bose(*cons[1:])
            assert [vv] == shape
            D = combine(shape, R, N, family)
        check(shape, D, k, lam)
        obj = f"O{first + i}"
        lines = [f"{'x'.join(f'C{m}' for m in shape)} ({v},{k},{lam})"]
        lines += [f"{' '.join(map(str, g))} {'+' if x > 0 else '-'}" for g, x in sorted(D.items())]
        (ROOT / "objects" / f"{obj}.txt").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
        print(obj, nid, family, shape, v, k, lam, "ok", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), *sys.argv[2:])
