# formal-conjectures collections survey (2026-10-22)

Same pipeline as [erdos.md](erdos.md), over every non-Erdős collection: 432 files, 767 open statements, scored by six Haiku agents (`data/results_collections.jsonl`).

Freshness check (`freshness.py`, files changed by open PRs): almost no top-40 file has a substantive open PR, unlike the Erdős list. Exceptions: `Arxiv/1601.03081` (crystals, PR #7051), `GreensOpenProblems/14` (a variant marked solved).

Haiku overrated famous problems again: Mahler's 3/2 problem (`Books/.../Equidistribution`), `Mathoverflow/17560` (four exponentials), `Wikipedia/MagicSquares`. `OEIS/113010` looks easy but hides digit sums of powers.

## Shortlist

| Problem | Statement | Status (searched 2026-10-22) |
|---|---|---|
| `Paper/CatchUpConjecture` | Catch-Up on {1..N} is a draw when N(N+1)/2 is even | Verified by computer to N = 28 (von Stengel); no proof or partial result found |
| `Arxiv/2507.17780/3` (TxGraffiti 3) | Regular graphs: independent domination number ≤ min maximal matching (= edge domination number) | Open since 2020; weaker γ ≤ γ_e proven for degree ≥ 7 via the Local Lemma (arXiv 2608.22498, Aug 2026) |
| `Mathoverflow/339137` = `GreensOpenProblems/28` | "Unfair 0-1 polynomial": nonnegative monic factors of a 0/1 polynomial are 0/1 | Small expert community (Ghidelli, Hare, Dvorsky); only special families done, latest arXiv 2608.19173 (trinomials 1 + ax² + x^k) |
