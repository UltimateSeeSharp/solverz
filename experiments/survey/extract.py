"""Join erdosproblems/data/problems.yaml with formal-conjectures Lean files.

Usage: python -I extract.py <src_dir> <out_dir>
<src_dir> holds clones of github.com/teorth/erdosproblems and github.com/google-deepmind/formal-conjectures.
Writes <out_dir>/candidates.jsonl (open problems whose statement is formalized) and batch_*.md for the classifier agents.
"""
import json
import re
import sys
from pathlib import Path

OPEN_STATES = {"open", "falsifiable", "verifiable", "decidable"}
OPEN_TAG = re.compile(r"@\[category research open")
# A declaration: optional docstring, attribute line(s), then theorem/lemma up to `:= by`/`:=`.
DECL = re.compile(
    r"(/--(?P<doc>(?:(?!-/).)*?)-/\s*)?@\[(?P<attr>[^\]]*(?:\[[^\]]*\][^\]]*)*)\]\s*"
    r"(?:theorem|lemma)\s+(?P<name>\S+)(?P<stmt>.*?):=",
    re.S,
)
REF_LINE = re.compile(r"^- \[", re.M)


def parse_yaml(text):
    """Minimal parser for the regular structure of problems.yaml."""
    problems, cur, section = [], None, None
    for line in text.splitlines():
        if line.startswith("- number:"):
            cur = {"number": line.split(":", 1)[1].strip().strip('"')}
            problems.append(cur)
            section = None
        elif cur is None or not line.strip():
            continue
        elif line.startswith("  ") and not line.startswith("    "):
            key, _, val = line.strip().partition(":")
            val = val.strip()
            if val:
                cur[key] = val.strip('"')
                section = None
            else:
                section = key
        elif line.startswith("    ") and section:
            key, _, val = line.strip().partition(":")
            cur[f"{section}.{key}"] = val.strip().strip('"')
    return problems


def lean_info(path):
    text = path.read_text(encoding="utf-8")
    header = re.search(r"/-!(.*?)-/", text, re.S)
    decls = []
    for m in DECL.finditer(text):
        attr = m["attr"]
        status = "open" if "research open" in attr else "solved" if "research solved" in attr else "other"
        if status == "other":
            continue
        decls.append({
            "name": m["name"],
            "status": status,
            "doc": " ".join((m["doc"] or "").split()),
            "lean": " ".join(m["stmt"].split()),
        })
    return {
        "refs": len(REF_LINE.findall(header[1])) if header else 0,
        "decls": decls,
    }


BATCHES = 5
MAIN_CHARS, VARIANT_CHARS = 1200, 300


def clip(s, n):
    return s if len(s) <= n else s[:n] + " …"


def write_batches(rows, out):
    """Compact markdown per batch: main open question in full, variants clipped."""
    size = -(-len(rows) // BATCHES)
    for b in range(BATCHES):
        lines = []
        for r in rows[b * size:(b + 1) * size]:
            main, *rest = r["open"]
            lines += [
                f"## Problem {r['number']}",
                f"status: {r['status']} | prize: {r['prize']} | tags: {r['tags']} | topic: {r['comments'] or '-'}"
                f" | solved variants: {r['n_solved_variants']}",
                f"MAIN ({main['name']}): {clip(main['doc'], MAIN_CHARS)}",
                f"LEAN: {clip(main['lean'], MAIN_CHARS)}",
            ]
            lines += [f"OPEN VARIANT ({v['name']}): {clip(v['doc'] or v['lean'], VARIANT_CHARS)}" for v in rest]
            lines.append("")
        (out / f"batch_{b + 1}.md").write_text("\n".join(lines), encoding="utf-8")


def main(src, out):
    problems = parse_yaml((src / "erdosproblems/data/problems.yaml").read_text(encoding="utf-8"))
    lean_dir = src / "formal-conjectures/FormalConjectures/ErdosProblems"
    rows = []
    for p in problems:
        if p.get("status.state") not in OPEN_STATES or p.get("formal_status.state") == "Lean":
            continue
        lean = lean_dir / f"{p['number']}.lean"
        if not lean.exists():
            continue
        info = lean_info(lean)
        open_decls = [d for d in info["decls"] if d["status"] == "open"]
        if not open_decls:
            continue
        rows.append({
            "number": int(p["number"]),
            "status": p["status.state"],
            "prize": p.get("prize", "no"),
            "tags": p.get("tags", "[]"),
            "comments": p.get("comments", ""),
            "refs": info["refs"],
            "n_solved_variants": sum(d["status"] == "solved" for d in info["decls"]),
            "open": open_decls,
        })
    out.mkdir(parents=True, exist_ok=True)
    with open(out / "candidates.jsonl", "w", encoding="utf-8") as f:
        for r in sorted(rows, key=lambda r: r["number"]):
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    states = {}
    for p in problems:
        states[p.get("status.state")] = states.get(p.get("status.state"), 0) + 1
    write_batches(sorted(rows, key=lambda r: r["number"]), out)
    print("all states:", states)
    print("candidates:", len(rows), "open decls:", sum(len(r["open"]) for r in rows))


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
