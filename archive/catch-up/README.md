# Catch-Up conjecture

Optimal play on {1..N} is a draw when 1 + … + N is even. **Current stage and next step: [state.md](state.md).**

## Problem

Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.

**Conjecture:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw. Lean: `CatchUp.Conjecture` in `lean/CatchUp/Statement.lean`, from formal-conjectures' `value_of_even_mul_succ_self_div_two`.

## Goals

- Explicit: prove `CatchUp.Conjecture` in Lean, or find a counterexample.
- Implicit: understand why perfect play draws (a describable drawing strategy or invariant); reusable Lean lemmas about the game (parity law, endgames); an exact solver that pushes the computational frontier (published: N = 28).

## Core difficulty

The low phase. On high sets (smallest number ≥ the spread) every turn is one pick, and even blocks there draw by a potential argument (L24, in Lean). {1..N} starts low: a turn can take several small numbers to make change, and the value depends on the whole set, not on local features. Every local rule, bounded invariant and single strategy tried for this phase fails as N grows (O4–O8, O11, O16, O17). A proof must control play while the set is low: an invariant the defender keeps while making change, or a reason the value cannot change as the set deforms into a high one. Sharpened (2026-10-28): after any opening of {1..N}, the opponent can make change with the bottom run {1..k} plus one number and leave a block with holes at height up to about √(2N); every route tried (closed families, potentials, deformations crossed breakpoint by breakpoint) fails there (O5, O20, O21). The strongest reformulation is L37: the player to move never loses by more than the largest gap of the numbers left (deficit included), which implies L1 and is tight exactly at intervals.

## Known

- Exhaustive search to N = 28: von Stengel, talk abstract, CGT Colloquium III, Lisbon 2019 ([ludicum.org/?p=4151](https://ludicum.org/?p=4151)). No paper, code or data found.
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- Original paper ([MPRA 108784](https://mpra.ub.uni-muenchen.de/108784/)): proves only the parity facts; notes that even-sum sets in general need not draw (multiset {2,2,2,3,3}).
- Endgames with 3–4 numbers left, case analysis: K. C. G. Feng, honors thesis, College of Staten Island 2024 ([pdf](https://www.math.csi.cuny.edu/Undergraduate/HonorsTheses/2024-feng.pdf)).
- No proof or partial proof found (searched 2026-10-22; again 2026-10-26).
- Nothing found on Catch-Up for sets other than {1..N}, on pairing strategies, or on position values by gap (searched 2026-10-22). Nothing on two-player differencing or partitioning games with a catch-up turn rule, or on gap bounds for the final margin (searched 2026-10-28; only one-player Karmarkar–Karp differencing and unrelated discrepancy and heap games). Misleading: a 2024 Brams article ([Open Access Government](https://www.openaccessgovernment.org/article/a-game-that-poses-a-challenge-to-artificial-intelligence/181077/)) says even-sum sets of 2–20 numbers draw; false for arbitrary sets ({1,3} is a first-player win).
## Agent rules

- Never edit `lean/CatchUp/Statement.lean` (approved statement).
- Experiments don't modify the engines (`solver/src/lib.rs`, `layered.rs`, `tiled.rs`, `cuda.rs`, `layered.cu`, `main.rs`); they add files in `solver/src/bin/` that use the library API ([solver/README.md](solver/README.md)).
- Compute per experiment: about 10 minutes and at most 16 GB RAM (of 32 GB, shared).

## Files

[state.md](state.md) · [lines.md](lines.md) · [log.md](log.md) · [backlog.md](backlog.md) · [obstructions.md](obstructions.md) · [blueprint.md](blueprint.md) · [solver/README.md](solver/README.md) · [results/](results/)
