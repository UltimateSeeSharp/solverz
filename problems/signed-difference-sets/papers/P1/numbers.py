"""Writes build/numbers.tex and build/sets.tex from instances.csv and corrections.md.

latexmk runs it before every build; every number in the text comes from here.
"""
import csv
import re
from collections import Counter
from pathlib import Path

PROBLEM = Path(__file__).resolve().parents[2]
BUILD = Path(__file__).parent / "build"
SIZE_BANDS = [(0, 50), (50, 100), (100, 200), (200, 500), (500, 10**9)]
OPEN_IN_SOURCE = "Open"
HE_WU = "He-Wu"


def fmt(n: int) -> str:
    return f"{n:,}".replace(",", "{,}")


def parse_key(key: str) -> tuple[int, int, int, list[int]]:
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    v, k, lam, shape = m.groups()
    return int(v), int(k), int(lam), [int(x) for x in shape.split(",")]


def group_tex(shape: list[int]) -> str:
    counts = Counter(shape)
    parts = [f"C_{{{m}}}" + (f"^{{{e}}}" if e > 1 else "") for m, e in counts.items()]
    return r" \times ".join(parts)


def main() -> None:
    BUILD.mkdir(exist_ok=True)
    rows = list(csv.DictReader(open(PROBLEM / "instances.csv", encoding="utf-8")))
    corrected = set(re.findall(r"N\d+", (PROBLEM / "corrections.md").read_text(encoding="utf-8")))
    source_open = [r for r in rows if r["source"].startswith(OPEN_IN_SOURCE)]
    ours = [r for r in rows if r["solution"]]
    # Settled by He-Wu: their four obstructions (none) and three constructions.
    prior = [r for r in source_open if not r["solution"] and r["id"] not in corrected
             and (r["status"] == "none" or r["evidence"].startswith(HE_WU))]
    # Our sets not yet approved as Solutions count as open in this baseline.
    pending = [r for r in source_open if r["status"] == "exists" and not r["solution"]
               and r["id"] not in corrected and r not in prior]
    open_after_hewu = len(source_open) - len(prior)
    still_open = [r for r in source_open if r["status"] == "open" or r in pending]
    by_z = Counter(r["solution"] for r in ours)

    macros = {
        "tableRows": len(rows),
        "sourceOpen": len(source_open),
        "openAfterHeWu": open_after_hewu,
        "ourRows": len(ours),
        "ourNone": sum(r["status"] == "none" for r in ours),
        "ourExists": sum(r["status"] == "exists" for r in ours),
        "corrections": len(corrected),
        "stillOpen": len(still_open),
        "pendingSets": len(pending),
    }
    lines = [rf"\newcommand{{\{name}}}{{{fmt(n)}}}" for name, n in macros.items()]
    settled = len(rows) - len(still_open)
    lines.append(rf"\newcommand{{\settledPercent}}{{{100 * settled / len(rows):.1f}}}")
    lines.append(rf"\newcommand{{\priorPercent}}{{{100 * (len(rows) - open_after_hewu) / len(rows):.1f}}}")
    for z, n in by_z.items():
        lines.append(rf"\expandafter\newcommand\csname zrows{z[1:]}\endcsname{{{fmt(n)}}}")
    for lo, hi in SIZE_BANDS:
        n = sum(lo <= parse_key(r["key"])[0] < hi for r in still_open)
        lines.append(rf"\expandafter\newcommand\csname openBelow{hi if hi < 10**9 else 'Max'}\endcsname{{{fmt(n)}}}")
    (BUILD / "numbers.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    found = sorted((r for r in ours if r["status"] == "exists"), key=lambda r: parse_key(r["key"])[:3])
    table = []
    for r in found:
        v, k, lam, shape = parse_key(r["key"])
        table.append(rf"{r['id']} & $({v}, {k}, {lam})$ & ${group_tex(shape)}$ & {r['solution']} \\")
    (BUILD / "sets.tex").write_text("\n".join(table) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
