# Problems

Candidate open problems, rated for this setup: one PC (8 cores, 32 GB RAM,
8 GB GPU), AI agents that write search code and proofs, and Lean 4 that
verifies every result without trusting compiled code (no `native_decide`).
New lists are added by hand: each problem gets one row, rated as below.
Sorted by score, highest first. Who is working on what:
[V3R1T4S](https://github.com/elder-plinius/V3R1T4S/tree/main/known-unknowns),
[EinsteinArena](https://einsteinarena.com/),
[HorizonMath](https://raw.githubusercontent.com/ewang26/HorizonMath/main/data/baselines.json),
[AlphaEvolve problems](https://github.com/google-deepmind/alphaevolve_repository_of_problems),
[FrontierMath open problems](https://epoch.ai/frontiermath/open-problems),
[Tao's AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems).

- **ID:** stable, from the source (`erdos/123`, `fc/Arxiv/2507.17780/3`,
  `table/cages-5-7`).
- **Problem:** plain English a non-mathematician can follow, at most 25
  words, linked to the source.
- **Kind:** `prove`, `find`, `bound`, `compute` (CLAUDE.md, Problem), or
  `none` (no finite check, or not well posed). **Framings:** other kinds
  that could also apply.
- **Fit** 1–5: 5 = clearly feasible on this machine, 1 = cluster-scale.
- **Lean** 1–5: 5 = an answer is cheap for Lean to check, 1 = needs a huge
  certificate or theory Mathlib lacks.
- **Idea** 1–5: 5 = hinges on a new idea experts have missed for years.
- **Crowding** 1–5: 5 = famous, or currently attacked by labs or AI crowds.
- **Score:** Fit + Lean + (6 − Idea) + (6 − Crowding); none for kind `none`.
- **Status:** `candidate`, `attacked` (link to its folder), `shelved`,
  `solved elsewhere`. **Checked:** date of the last freshness check.

| ID | Problem | Kind | Framings | Fit | Lean | Idea | Crowding | Score | Status | Checked |
|---|---|---|---|---|---|---|---|---|---|---|
| fc/Paper/CatchUpConjecture | [Catch-Up](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean) on {1..N}: with perfect play, is the game a draw whenever 1 + … + N is even? | prove | — | 4 | 4 | 4 | 3 | 13 | [attacked](problems/catch-up/README.md) | 2026-10-28 |
