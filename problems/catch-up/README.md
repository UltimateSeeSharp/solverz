# Catch-Up conjecture

Idea log, failures included. Nothing here is trusted until proven in `lean/`.

## Problem

Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.

**Conjecture:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw. Lean statement: formal-conjectures `FormalConjectures/Paper/CatchUpConjecture.lean`, `value_of_even_mul_succ_self_div_two` (read-through: matches the rules).

## Known

- Exhaustive search to N = 28: von Stengel, talk abstract, CGT Colloquium III, Lisbon 2019 ([ludicum.org/?p=4151](https://ludicum.org/?p=4151)). No paper, code or data found.
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- No proof or partial proof found (searched 2026-10-22).

## Our solver

`solver/` (Rust): mirrors Lean `valueAux` with a 2-bit memo table; cross-checked against an independent turn-based reference on all subsets of {1..8} and against A278587. N = 24 in 25 s, single core.

## Observations (N ≤ 24)

- Draw for every even-total N, matching the literature.
- Player 2 wins only at N = 9, 10, 14, 18; from N = 21 player 1 wins with opening 3 (N ≡ 1 mod 4) or 2 (N ≡ 2 mod 4).
- **Every opening move draws for even-total N ≥ 12** (exceptions only below: N = 3 opening 2, N = 4 openings 3–4, N = 7 openings 5–7, N = 11 opening 10). Both drawing strategies are robust, so a simple description may exist.

## Next

1. Reproduce N = 25..28, then N = 31 (new; about 17 GB table). N = 32 needs a smaller encoding.
2. Look for a simple drawing strategy: test candidate rules (e.g. "pick the largest number that catches up") against a perfect opponent with the solver; a rule that never loses for all N ≤ 24 is a proof target.
