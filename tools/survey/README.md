# Problem survey

Finds open, Lean-formalized problems bottlenecked on reasoning. Findings: [erdos.md](erdos.md), [collections.md](collections.md).

## Run

Stdlib Python only; run with `python -I`. `<src>` holds clones of [teorth/erdosproblems](https://github.com/teorth/erdosproblems) and [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures); `<out>` is a scratch folder.

1. `python -I extract.py erdos|collections <src> <out>` writes `candidates.jsonl` and `batch_*.md`.
2. One Haiku agent per batch, prompt in [classify-prompt.md](classify-prompt.md), writes `<out>/results_<i>.jsonl`.
3. `python -I rank.py <out> 40` validates and ranks (2·tractability + (6 − fame) + elementary + lean_friendly, compute-bound excluded).
4. `python -I freshness.py <out>/ranked.jsonl <open_pr_files.jsonl> 40` flags candidates touched by open formal-conjectures PRs (the `gh` command is in the script's docstring).
5. Review the top by hand: `python -I show.py <formal-conjectures>/FormalConjectures <id>...` prints statements and known results; then check forum threads and arXiv.

`data/` holds the merged agent scores of both runs (2026-10-22).
