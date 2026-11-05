"""Objects and Lean answers for found sets (standard library only).

`answer.py object <run output> <instance id> <object id>`: writes objects/O<id>.txt from
the run's line for that Instance (`id key yes nodes time coords± …`).
`answer.py lean <object id> <instance id>`: writes lean/SignedDifferenceSets/Answer/N<id>.lean,
whose `hasSDS` Lean checks by `decide`.
`answer.py fast <object id> <instance id>`: the same through `checkSet` and `decide +kernel`,
for sets too large for `decide`.
"""
import csv
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


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    {"object": write_object, "lean": write_lean, "fast": write_fast}[cmd](*args)
