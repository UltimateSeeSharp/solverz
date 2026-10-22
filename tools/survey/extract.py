"""Collect open formal-conjectures statements into batches for the classifier agents.

Usage: python -I extract.py erdos|collections <src_dir> <out_dir>
<src_dir> holds clones of github.com/teorth/erdosproblems and github.com/google-deepmind/formal-conjectures.
  erdos:       join erdosproblems/data/problems.yaml with the ErdosProblems Lean files.
  collections: every other collection; open/solved status comes from the Lean `category` tags.
Writes <out_dir>/candidates.jsonl and batch_*.md.
"""
import json
import re
import sys
from pathlib import Path

OPEN_STATES = {"open", "falsifiable", "verifiable", "decidable"}
ERDOS_DIR = "ErdosProblems"
# A declaration: optional docstring, attribute line(s), then theorem/lemma up to `:= by`/`:=`.
DECL = re.compile(
    r"(/--(?P<doc>(?:(?!-/).)*?)-/\s*)?@\[(?P<attr>[^\]]*(?:\[[^\]]*\][^\]]*)*)\]\s*"
    r"(?:theorem|lemma)\s+(?P<name>\S+)(?P<stmt>.*?):=",
    re.S,
)
HEADER = re.compile(r"/-!(.*?)-/", re.S)
REF_LINE = re.compile(r"^- \[", re.M)
BATCH_CHARS = 55_000
MAIN_CHARS, VARIANT_CHARS, HEADER_CHARS = 1200, 300, 300


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


def squash(s):
    return " ".join((s or "").split())


def lean_info(path):
    text = path.read_text(encoding="utf-8")
    header = HEADER.search(text)
    decls = []
    for m in DECL.finditer(text):
        attr = m["attr"]
        status = "open" if "research open" in attr else "solved" if "research solved" in attr else None
        if status:
            decls.append({"name": m["name"], "status": status, "doc": squash(m["doc"]), "lean": squash(m["stmt"])})
    return {
        "header": squash(header[1]) if header else "",
        "refs": len(REF_LINE.findall(header[1])) if header else 0,
        "decls": decls,
    }


def row(id_, status, meta, info):
    open_decls = [d for d in info["decls"] if d["status"] == "open"]
    return open_decls and {
        "id": id_,
        "status": status,
        "meta": meta,
        "refs": info["refs"],
        "n_solved_variants": sum(d["status"] == "solved" for d in info["decls"]),
        "open": open_decls,
    }


def erdos_rows(src):
    problems = parse_yaml((src / "erdosproblems/data/problems.yaml").read_text(encoding="utf-8"))
    lean_dir = src / "formal-conjectures/FormalConjectures" / ERDOS_DIR
    for p in problems:
        lean = lean_dir / f"{p['number']}.lean"
        if p.get("status.state") in OPEN_STATES and p.get("formal_status.state") != "Lean" and lean.exists():
            meta = f"prize: {p.get('prize', 'no')} | tags: {p.get('tags', '[]')} | topic: {p.get('comments') or '-'}"
            yield row(int(p["number"]), p["status.state"], meta, lean_info(lean))


def collection_rows(src):
    root = src / "formal-conjectures/FormalConjectures"
    for lean in sorted(root.rglob("*.lean")):
        rel = lean.relative_to(root)
        if rel.parts[0] != ERDOS_DIR and len(rel.parts) > 1:
            info = lean_info(lean)
            yield row(rel.with_suffix("").as_posix(), "open", f"source: {clip(info['header'], HEADER_CHARS)}", info)


def clip(s, n):
    return s if len(s) <= n else s[:n] + " …"


def render(r):
    main, *rest = r["open"]
    lines = [
        f"## Problem {r['id']}",
        f"status: {r['status']} | {r['meta']} | solved variants: {r['n_solved_variants']}",
        f"MAIN ({main['name']}): {clip(main['doc'], MAIN_CHARS)}",
        f"LEAN: {clip(main['lean'], MAIN_CHARS)}",
    ]
    lines += [f"OPEN VARIANT ({v['name']}): {clip(v['doc'] or v['lean'], VARIANT_CHARS)}" for v in rest]
    return "\n".join(lines) + "\n"


def write_batches(rows, out):
    """Greedy split into batches of about BATCH_CHARS; returns the problem count per batch."""
    batches, cur = [], []
    for r in rows:
        if cur and sum(map(len, cur)) + len(render(r)) > BATCH_CHARS:
            batches.append(cur)
            cur = []
        cur.append(render(r))
    batches.append(cur)
    for i, b in enumerate(batches, 1):
        (out / f"batch_{i}.md").write_text("\n".join(b), encoding="utf-8")
    return [len(b) for b in batches]


def main(mode, src, out):
    rows = [r for r in (erdos_rows(src) if mode == "erdos" else collection_rows(src)) if r]
    out.mkdir(parents=True, exist_ok=True)
    with open(out / "candidates.jsonl", "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    sizes = write_batches(rows, out)
    print("candidates:", len(rows), "open decls:", sum(len(r["open"]) for r in rows), "batches:", sizes)


if __name__ == "__main__":
    main(sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]))
