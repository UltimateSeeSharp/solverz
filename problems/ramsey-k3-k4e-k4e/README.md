# R(K₃, K₄−e, K₄−e)

Is the 3-colour Ramsey number R(K₃, K₄−e, K₄−e) 21 or 22?
**Status:** open; search engine being built.

## Solutions
None yet ([solutions.md](solutions.md)).

## Problem
Colour each edge of K₂₁ (21 points, every pair joined) 1, 2 or 3 so that
colour 1 has no triangle and neither colour 2 nor colour 3 has a K₄−e
(4 points with at least 5 of their 6 edges in that colour). Such a
colouring exists iff R(K₃, K₄−e, K₄−e) = 22; otherwise it is 21.
**Goal:** such a colouring of K₂₁ exists, Lean `RamseyK3K4eK4e.Goal`,
approved 2026-10-30.

## Literature
- Radziszowski, Small Ramsey Numbers, DS1 revision 18 (EJC, 2026-04-24):
  21 ≤ R(K₃, K₄−e, K₄−e) ≤ 22 [ShWR][LidP]. Opened 2026-10-30.
- Shetler, Wurtz, Radziszowski 2012 ([arXiv:1201.0554](https://arxiv.org/abs/1201.0554)):
  lower bound 21 from a 20-point colouring printed in Figure 3, obtained by
  splitting the unique (J₇, K₃; 20)-good graph; upper bound 27; also
  R(K₃, K₃, K₄−e) = 17 by SAT and exhaustive splitting. Opened 2026-10-30.
- Lidický, Pfender 2017 ([arXiv:1704.03592](https://arxiv.org/abs/1704.03592)),
  Theorem 8: flag-algebra upper bound 22 (computed ⌊22.70⌋), down from 27.
- Boza, Dybizbański, Dzido 2012 (EJC 19(4) P47): R(K₃+e, K₄−e, K₄−e) =
  R(K₃, K₄−e, K₄−e). Abstract opened 2026-10-30.
- Wesley 2025 ([arXiv:2509.03784](https://arxiv.org/abs/2509.03784)): SAT on
  structured colourings for neighbouring cases (R(K₄, K₄−e, K₄−e) ≥ 35); not this one.
- AI attention: none found (2026-10-30; AlphaEvolve, FunSearch,
  PatternBoost, LLM, reinforcement learning; the formal-conjectures,
  HorizonMath, EinsteinArena and AlphaEvolve problem lists). Nearest:
  OpenAI's multicolour triangle Ramsey asymptotics (2026-08), a different
  question.

## Working on it
State: [state.md](state.md) (the current work; it may hold unchecked proposals).
Kind: find. Modules: find. Estimate: as SAT, 630 variables (210 edges × 3 colours) and
about 74,000 clauses, memory trivial; hardness unknown, minutes to weeks
depending on symmetry breaking. Lean: 1,330 triangles and 5,985 four-point
sets through a list-based checker proved correct. If no colouring exists
the value is 21, but that needs an exhaustive proof whose certificate is
impractical for Lean's kernel.
