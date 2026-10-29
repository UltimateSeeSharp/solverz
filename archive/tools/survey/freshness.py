"""Flag ranked candidates whose Lean file is touched by an open formal-conjectures PR.

Usage: python -I freshness.py <ranked.jsonl> <open_pr_files.jsonl> [top_n]
Get open_pr_files.jsonl with:
  gh api graphql --paginate -f query='query($endCursor: String) { repository(owner: "google-deepmind",
    name: "formal-conjectures") { pullRequests(states: OPEN, first: 50, after: $endCursor) {
    pageInfo { hasNextPage endCursor } nodes { number title createdAt files(first: 50) { nodes { path } } } } } }'
    --jq '.data.repository.pullRequests.nodes[] | {number, title, createdAt, files: [.files.nodes[].path]}'
"""
import json
import sys
from pathlib import Path

ROOT = "FormalConjectures"
ERDOS_DIR = "ErdosProblems"


def lean_path(r):
    # Erdős results are keyed by "number", collection results by "id".
    return f"{ROOT}/{r['id']}.lean" if "id" in r else f"{ROOT}/{ERDOS_DIR}/{r['number']}.lean"


def main(ranked_file, prs_file, top_n):
    sys.stdout.reconfigure(encoding="utf-8")
    by_file = {}
    for line in Path(prs_file).read_text(encoding="utf-8").splitlines():
        pr = json.loads(line)
        for f in pr["files"]:
            by_file.setdefault(f, []).append(pr)
    ranked = [json.loads(l) for l in Path(ranked_file).read_text(encoding="utf-8").splitlines()][:top_n]
    for i, r in enumerate(ranked, 1):
        for pr in by_file.get(lean_path(r), []):
            print(f"rank {i:>2}  {lean_path(r)}  PR {pr['number']}  {pr['createdAt'][:10]}  {pr['title'][:90]}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 60)
