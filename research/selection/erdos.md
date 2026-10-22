# Erdős problems survey (2026-10-22)

Goal: find open problems bottlenecked on reasoning (not compute) that we could realistically attack.

## Method

1. Joined Tao's database ([teorth/erdosproblems](https://github.com/teorth/erdosproblems), 1221 problems) with DeepMind's Lean statements ([formal-conjectures](https://github.com/google-deepmind/formal-conjectures)).
2. Kept problems marked open, with a Lean statement and no Lean solution: 437 problems, 693 open statements incl. variants.
3. Five Haiku agents scored each: bottleneck, elementary, fame, tractability, Lean-friendliness. Ranked by 2·tractability + (6 − fame) + elementary + lean_friendly, compute-bound excluded.
4. Reviewed the top ~40 by hand, then read the erdosproblems.com forum threads of the shortlist.

Scripts: this folder; raw scores: `data/results_erdos.jsonl`. Haiku scores are a rough pre-filter; it overrated famous problems (#159, #1003, #850).

## Findings

- **The long tail is a race.** Since 2025, many people point frontier AI (GPT-5.x/6, Gemini Deep Think, Claude, Aristotle, AlphaProof) at these problems; Tao comments on many; the forum suspended new comments. In 3 weeks of Oct 2026 alone, open PRs mark #1212 and #306 solved and add partial proofs for #422, #642, #939.
- **The databases lag.** Both sources still listed #488 as open, but it was disproved on 2026-09-05 ([PR #5297](https://github.com/google-deepmind/formal-conjectures/pull/5297), independently replayed by a reviewer).
- **Uncrowded usually means hard machinery.** #985 needs analytic number theory (settled only under GRH); #614 contains the C4 Turán number; #889 is sieve-type.

## Shortlist verdicts

| # | Question (short) | Verdict |
|---|---|---|
| 488 | Multiples of a finite set: density can't double | **Disproved** (Gessel, smooth-number counterexample, Lean-checked) |
| 686 | Is N a ratio of two k-term consecutive products? | Crowded; case-by-case progress for N = 4, 25, …; general k open |
| 396 | k+1 consecutive numbers dividing C(2n, n) | Crowded; minimal witnesses computed to k = 14; density bounds only |
| 389 | n(n+1)…(n+k−1) divides the next k-block | Crowded; computational only, no proof ideas |
| 624 | Covering function on subsets, H(n) − log₂n → ∞ | 3 comments; small cases by SAT; asymptotics untouched since Erdős–Hajnal / Alon |
| 614 | Min edges so every k+2 vertices have a degree-k vertex | 1 comment; reduces to Turán problems, k = 2 is the open C4 case |
| 985 | A prime primitive root below every prime p | 2 comments; open unconditionally, true under GRH for large p |
| 889 | v₀(n) → ∞ (new prime factors of n + k) | 2 comments; a sibling variant proven in Lean, main problem sieve-hard |
