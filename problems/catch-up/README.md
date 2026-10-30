# Catch-Up conjecture

Optimal play on {1..N} is a draw when 1 + … + N is even. Now: [state.md](state.md).

## Problem
Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.
**Goal:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw; claim C1, Lean `CatchUp.Conjecture` in `lean/CatchUp/Statement.lean` (from formal-conjectures' `value_of_even_mul_succ_self_div_two`).
Kind: prove.

## Literature
- Exhaustive search to N = 28: von Stengel, talk abstract, CGT Colloquium III, Lisbon 2019 ([ludicum.org/?p=4151](https://ludicum.org/?p=4151)). No paper, code or data found.
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- Original paper ([MPRA 108784](https://mpra.ub.uni-muenchen.de/108784/)): proves only the parity facts; notes that even-sum sets in general need not draw (multiset {2,2,2,3,3}).
- Endgames with 3–4 numbers left, case analysis: K. C. G. Feng, honors thesis, College of Staten Island 2024 ([pdf](https://www.math.csi.cuny.edu/Undergraduate/HonorsTheses/2024-feng.pdf)).
- No proof or partial proof found (searched 2026-10-22; again 2026-10-26).
- Nothing found on Catch-Up for sets other than {1..N}, on pairing strategies, or on position values by gap (searched 2026-10-22). Nothing on two-player differencing or partitioning games with a catch-up turn rule, or on gap bounds for the final margin (searched 2026-10-28; only one-player Karmarkar–Karp differencing and unrelated discrepancy and heap games). Misleading: a 2024 Brams article ([Open Access Government](https://www.openaccessgovernment.org/article/a-game-that-poses-a-challenge-to-artificial-intelligence/181077/)) says even-sum sets of 2–20 numbers draw; false for arbitrary sets ({1,3} is a first-player win).
