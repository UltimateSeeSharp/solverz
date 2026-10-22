# Catch-Up conjecture

Optimal play on {1..N} is a draw when 1 + … + N is even. **Current stage and next step: [state.md](state.md).** Nothing here is trusted until proven in `lean/`.

## Problem

Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.

**Conjecture:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw. Lean: `CatchUp.Conjecture` in `lean/CatchUp/Statement.lean`, ported from formal-conjectures `value_of_even_mul_succ_self_div_two`; reviewed and approved by the user 2026-10-22.

## Goals

- Explicit: prove `CatchUp.Conjecture` in Lean, or find a counterexample.
- Implicit: understand why perfect play draws (a describable drawing strategy or invariant); reusable Lean lemmas about the game (parity law, endgames); an exact solver that pushes the computational frontier (published: N = 28).

## Known

- Exhaustive search to N = 28: von Stengel, talk abstract, CGT Colloquium III, Lisbon 2019 ([ludicum.org/?p=4151](https://ludicum.org/?p=4151)). No paper, code or data found.
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- Original paper ([MPRA 108784](https://mpra.ub.uni-muenchen.de/108784/)): proves only the parity facts; notes that even-sum sets in general need not draw (multiset {2,2,2,3,3}).
- Endgames with 3–4 numbers left, case analysis: K. C. G. Feng, honors thesis, College of Staten Island 2024 ([pdf](https://www.math.csi.cuny.edu/Undergraduate/HonorsTheses/2024-feng.pdf)).
- No proof or partial proof found (searched 2026-10-22).

## Agent rules

- Never edit `lean/CatchUp/Statement.lean` (approved statement).
- The solver engines (`solver/src/lib.rs`, `layered.rs`, `tiled.rs`, `gpu.rs`, `tile.wgsl`, `main.rs`) belong to the main session; experiments add new files in `solver/src/bin/` and use the library API ([solver/README.md](solver/README.md)).
- Compute per experiment: about 10 minutes and at most 16 GB RAM (the machine has 32 GB, shared).

## Files

- [state.md](state.md): stage, results, open threads, next step, awaiting review. Read first; rewritten every iteration.
- [log.md](log.md): every attempt, failures included. [backlog.md](backlog.md): open ideas. [obstructions.md](obstructions.md): what's ruled out. [blueprint.md](blueprint.md): lemmas toward a proof.
- [solver/README.md](solver/README.md): engines and experiments. [results/](results/): curated outputs with run metadata.
