"""Objects and Lean answers for found sets (standard library only).

`answer.py object <run output> <instance id> <object id>`: writes objects/O<id>.txt from
the run's line for that Instance (`id key yes nodes time coords± …`).
`answer.py lean <object id> <instance id>`: writes lean/SignedDifferenceSets/Answer/N<id>.lean,
whose `hasSDS` Lean checks by `decide`.
`answer.py fast <object id> <instance id>`: the same through `checkSet` and `decide +kernel`,
for sets too large for `decide`.
`answer.py contract <instance id> <d1,…,dr>`: writes Answer/N<id>.lean proving no SDS by
contraction along ∏ ZMod mᵢ → ∏ ZMod dᵢ (`not_hasSDS_of_noVector`, `decide +kernel`); a search
of more than SPLIT_NODES nodes is split into one kernel check per prefix (`noVector_of_top`).
"""
import csv
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ANSWER_DIR = ROOT / "lean" / "SignedDifferenceSets" / "Answer"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


def instance_key(instance: str) -> str:
    with open(ROOT / "instances.csv", newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["id"] == instance:
                return row["key"]
    sys.exit(f"{instance} not in instances.csv")


def parse_key(key: str):
    m = KEY.fullmatch(key)
    v, k, lam = map(int, m.groups()[:3])
    return v, k, lam, [int(x) for x in m.group(4).split(",")]


def write_object(run_file: str, instance: str, obj: str) -> None:
    key = instance_key(instance)
    v, k, lam, shape = parse_key(key)
    for line in open(run_file, encoding="utf-8"):
        parts = line.split()
        if parts[:3] == [instance, key, "yes"]:
            lines = [f"{'x'.join(f'C{m}' for m in shape)} ({v},{k},{lam})"]
            for t in parts[5:]:
                lines.append(f"{' '.join(t[:-1].split('.'))} {t[-1]}")
            (ROOT / "objects" / f"{obj}.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
            return
    sys.exit(f"no set for {instance} in {run_file}")


def read_object(obj: str):
    first, *rest = (ROOT / "objects" / f"{obj}.txt").read_text(encoding="utf-8").splitlines()
    shape = [int(m) for m in re.findall(r"C(\d+)", first.split()[0])]
    v, k, lam = map(int, re.search(r"\((\d+),(\d+),(-?\d+)\)", first).groups())
    signs = {}
    for line in rest:
        *coords, sign = line.split()
        signs[tuple(map(int, coords))] = 1 if sign == "+" else -1
    return shape, v, k, lam, signs


def table(shape, signs, prefix=()):
    """Nested `![…]` literal indexed by the coordinates, first factor outermost."""
    if len(prefix) == len(shape):
        return str(signs.get(prefix, 0))
    entries = [table(shape, signs, prefix + (c,)) for c in range(shape[len(prefix)])]
    if prefix:
        return f"![{', '.join(entries)}]"
    # Top level: one outer entry per line (16 signs per line for a cyclic group).
    step = 16 if len(shape) == 1 else 1
    rows = [", ".join(entries[i : i + step]) for i in range(0, len(entries), step)]
    return "![" + ",\n    ".join(rows) + "]"


def write_lean(obj: str, instance: str) -> None:
    shape, v, k, lam, signs = read_object(obj)
    key = instance_key(instance)
    assert parse_key(key) == (v, k, lam, shape), f"{obj} does not answer {key}"
    group = " × ".join(f"ZMod {m}" for m in shape)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    proj = ["p"] if len(shape) == 1 else [f"p{'.2' * i}.1" for i in range(len(shape) - 1)] + [
        f"p{'.2' * (len(shape) - 1)}"
    ]
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    text = f"""module

public import SignedDifferenceSets.Check

/-!
# {instance}: a ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05). The set is object {obj}
(`objects/{obj}.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

/-- Object {obj}: the sign of each element, first coordinate outermost. -/
def sds : {group} → SignType := fun p =>
  ({table(shape, signs)})
    {' '.join(proj)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS {k} {lam_lean} sds := by decide

/-- {instance}: {pretty} has a signed difference set with parameters ({v}, {k}, {lam}). -/
theorem hasSDS : HasSDS ({group}) {k} {lam_lean} := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8")


def masks(shape, signs):
    """Bit masks (plus, minus) over the element numbers of `Indexed`: mixed radix, first
    coordinate most significant."""
    plus = minus = 0
    for coords, sign in signs.items():
        i = 0
        for c, m in zip(coords, shape):
            i = i * m + c
        if sign > 0:
            plus |= 1 << i
        else:
            minus |= 1 << i
    return plus, minus


def write_fast(obj: str, instance: str) -> None:
    shape, v, k, lam, signs = read_object(obj)
    key = instance_key(instance)
    assert parse_key(key) == (v, k, lam, shape), f"{obj} does not answer {key}"
    group = " × ".join(f"ZMod {m}" for m in shape)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    plus, minus = masks(shape, signs)
    text = f"""module

public import SignedDifferenceSets.SetCheck

/-!
# {instance}: a ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05). The set is object {obj}
(`objects/{obj}.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object {obj}'s plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := {plus:#x}

set_option linter.style.longLine false in
/-- Object {obj}'s minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := {minus:#x}

/-- Object {obj}: the sign of each element. -/
def sds : {group} → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS {k} {lam_lean} sds :=
  isSDS_of_checkSet (G := {group}) (P := plus) (N := minus) (by decide +kernel)

/-- {instance}: {pretty} has a signed difference set with parameters ({v}, {k}, {lam}). -/
theorem hasSDS : HasSDS ({group}) {k} {lam_lean} := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8")


# The kernel keeps about 0.1 MB per search node of one declaration (N79: 51,596 nodes, 7.5 GB).
SPLIT_NODES = 60_000
BRANCH_NODES = 20_000


def prefix_nodes(n, c, Q, s, depth):
    """Search nodes below each prefix of `depth` coordinates that `noVectorTop` leaves to its
    own check, mirroring `go` (a missing prefix fails the build, it cannot prove anything)."""
    def cut(rem, sm, sq):
        r, d = Q - sq, s - sm
        return r < 0 or rem * r < d * d or rem * c < abs(d)

    def size(rem, top, sm, sq):
        if rem == 0 or cut(rem, sm, sq):
            return 1
        return 1 + sum(size(rem - 1, top, sm + x, sq + x * x)
                       for x in range(-top, top + 1) if x * x <= Q - sq)

    counts = {}

    def walk(prefix, rem, top, sm, sq):
        if len(prefix) == depth:
            counts[tuple(prefix)] = size(rem, top, sm, sq)
        elif rem > 0 and not cut(rem, sm, sq):
            for x in range(-top, top + 1):
                if x * x <= Q - sq:
                    walk(prefix + [x], rem - 1, top, sm + x, sq + x * x)

    if not cut(n, 0, 0):
        for x in range(-c, c + 1):
            if x * x <= Q:
                walk([x], n - 1, abs(x), x, x * x)
    return counts


def proj_term(shape, divisors):
    """`Proj` built factor by factor, products nested to the right like the key's type."""
    casts = [f".cast {d} (by norm_num)" for d in divisors]
    term = casts[-1]
    for cast in reversed(casts[:-1]):
        term = f".prod ({cast})\n    ({term})"
    return term


def write_contract(instance: str, divisors: str) -> None:
    key = instance_key(instance)
    v, k, lam, shape = parse_key(key)
    ds = [int(d) for d in divisors.split(",")]
    assert len(ds) == len(shape) and all(m % d == 0 for m, d in zip(shape, ds)), divisors
    n = math.prod(ds)
    c, s = v // n, math.isqrt(k + lam * (v - 1))
    assert s * s == k + lam * (v - 1), "F1 fails"
    group = " × ".join(f"ZMod {m}" for m in shape)
    quotient = " × ".join(f"ZMod {d}" for d in ds)
    pretty = " × ".join(f"C{str(m).translate(SUB)}" for m in shape)
    pretty_h = " × ".join(f"C{str(d).translate(SUB)}" for d in ds if d > 1)
    lam_lean = f"({lam})" if lam < 0 else str(lam)
    q = k + lam * (c - 1)
    total = sum(prefix_nodes(n, c, q, s, 1).values()) + 1
    search = "(by decide +kernel)"
    split = ""
    if total > SPLIT_NODES:
        depth = next(d for d in range(2, n + 1)
                     if max(prefix_nodes(n, c, q, s, d).values()) <= BRANCH_NODES)
        prefixes = list(prefix_nodes(n, c, q, s, depth))
        lists = ",\n    ".join("[" + ", ".join(map(str, p)) + "]" for p in prefixes)
        checks = "\n\n".join(
            f"set_option maxRecDepth 100000 in\n"
            f"theorem below_{i} : check [{', '.join(map(str, p))}] = true := by\n"
            "  decide +kernel" for i, p in enumerate(prefixes))
        cases = " | ".join("rfl" for _ in prefixes)
        names = ", ".join(f"below_{i}" for i in range(len(prefixes)))
        split = f"""
/-- `below` with this Instance's search arguments (those `not_hasSDS_of_noVector` asks for). -/
abbrev check (p : List ℤ) : Bool :=
  below (Indexed.size ({quotient})) (Indexed.addIdx ({quotient})) ({c} : ℕ)
    (({k} : ℕ) + ({lam_lean} : ℤ) * (({c} : ℕ) - 1)) (({lam_lean} : ℤ) * ({c} : ℕ)) ({k} : ℕ) {s}

/-- The prefixes of {depth} coordinates whose subtrees are checked one by one ({total} nodes in
all, at most {BRANCH_NODES} per check), from `solver/answer.py`. -/
def prefixes : List (List ℤ) :=
  [{lists}]

{checks}
"""
        search = f"""(noVector_of_top (P := prefixes) (d := {depth - 1}) (by decide)
      (by decide +kernel) fun p hp => by
        simp only [prefixes, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with {cases}
        exacts [{names}])"""
    text = f"""module

public import SignedDifferenceSets.ContractionCheck

/-!
# {instance}: no ({v}, {k}, {lam}) SDS in {pretty}

Open in Gordon's table (`{key}`, 2026-11-05).
Contract along {pretty} → {pretty_h} (F3): fibres of {c} elements, so the coset
sums lie in [−{c}, {c}], have square sum {k} + {lam} · {c - 1} = {k + lam * (c - 1)}, sum ±{s} and
autocorrelation {lam} · {c} = {lam * c} at every shift ≠ 0; `noVector` (`decide +kernel`)
finds no such vector. Quotient from E5; this file is generated by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.{instance}

/-- The projection {pretty} → {pretty_h}, factor by factor. -/
def proj : Proj ({group}) ({quotient}) :=
  {proj_term(shape, ds)}
{split}
set_option maxRecDepth 100000 in
-- `decide +kernel` runs the vector search.
/-- {instance}: {pretty} has no signed difference set with parameters ({v}, {k}, {lam}). -/
theorem not_hasSDS : ¬ HasSDS ({group}) {k} {lam_lean} :=
  not_hasSDS_of_noVector proj {c} {s} (by simp [Fintype.card_prod, ZMod.card])
    (by norm_num [Fintype.card_prod, ZMod.card]) {search}

end SignedDifferenceSets.Answer.{instance}
"""
    (ANSWER_DIR / f"{instance}.lean").write_text(text, encoding="utf-8")


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    {"object": write_object, "lean": write_lean, "fast": write_fast, "contract": write_contract}[
        cmd
    ](*args)
