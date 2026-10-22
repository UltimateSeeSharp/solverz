"""Merge agent results and rank the sweet spot.

Usage: python -I rank.py <out_dir> [top_n]
Reads candidates.jsonl (from extract.py) + results*.jsonl, writes ranked.md and ranked.jsonl.
"""
import json
import sys
from pathlib import Path

SCORES = ("elementary", "fame", "tractability", "lean_friendly")
EXCLUDED_BOTTLENECK = "computation"


def rid(r):
    # Erdős results are keyed by "number", collection results by "id".
    return r["id"] if "id" in r else r["number"]


def score(r):
    # Tractability counts double; fame is inverted (obscure = good).
    return 2 * r["tractability"] + (6 - r["fame"]) + r["elementary"] + r["lean_friendly"]


def main(out, top_n):
    cands = {}
    for line in (out / "candidates.jsonl").read_text(encoding="utf-8").splitlines():
        c = json.loads(line)
        cands[rid(c)] = c
    results, bad = {}, []
    for f in sorted(out.glob("results*.jsonl")):
        for i, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
            if not line.strip():
                continue
            try:
                r = json.loads(line)
                assert all(isinstance(r[k], int) and 1 <= r[k] <= 5 for k in SCORES)
                results[rid(r)] = r
            except (ValueError, KeyError, AssertionError):
                bad.append(f"{f.name}:{i}")
    missing = sorted(set(cands) - set(results))
    print(f"classified {len(results)}/{len(cands)}; malformed lines: {bad or 'none'}; missing: {missing or 'none'}")

    ranked = sorted(
        (r for r in results.values() if r["bottleneck"] != EXCLUDED_BOTTLENECK and rid(r) in cands),
        key=lambda r: (-score(r), r["fame"], str(rid(r))),
    )
    with open(out / "ranked.jsonl", "w", encoding="utf-8") as f:
        for r in ranked:
            f.write(json.dumps({**r, "score": score(r), "status": cands[rid(r)]["status"]}, ensure_ascii=False) + "\n")
    lines = ["| # | score | T | F | E | L | status | summary | best variant |", "|---|---|---|---|---|---|---|---|---|"]
    for r in ranked[:top_n]:
        lines.append(
            f"| {rid(r)} | {score(r)} | {r['tractability']} | {r['fame']} | {r['elementary']} | {r['lean_friendly']}"
            f" | {cands[rid(r)]['status']} | {r['summary']} | `{r['best_variant']}` |"
        )
    (out / "ranked.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main(Path(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 30)
