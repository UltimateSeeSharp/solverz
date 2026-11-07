# Catch-Up conjecture

Optimal play on {1..N} is a draw when 1 + … + N is even.
**Status:** open; partial results.

## Solutions
None yet ([solutions.md](solutions.md)).

## Problem
Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.
**Goal:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw; claim C1, Lean `CatchUp.Goal` in `lean/CatchUp/Statement.lean` (from formal-conjectures' `value_of_even_mul_succ_self_div_two`).

## Literature
- von Stengel computed optimal play through N = 34: a winning opening is unique, and from N = 21 odd totals are won by an opening ≤ 3 (LSE PhD seminar abstract, 22 Feb 2019, [pdf p. 5](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5); earlier to N = 28: CGT Colloquium III talk, Lisbon 2019, [ludicum.org/?p=4151](https://ludicum.org/?p=4151)). A private report reaches N = 38 (2024, via catch-up-research CU-L043; not public).
- [catch-up-research](https://github.com/bocowgill-collaborations/catch-up-research) (Apache 2.0; read at b0853b4, 2026-10-30; no newer commits on 2026-11-04): 117 Lean modules on Lean and Mathlib v4.27, no sorry, extra axiom or native_decide (kernel decide only, axiom audit); the same valueAux and conjecture as ours, still open there. Its main route is our C31(b); its Lean results and dead approaches are in our claims, citing it. All 117 modules are ported into our build (2026-11-04, v4.35; `lean/NOTICE.md`), among them the verified evaluator (`lean/CatchUp/Executable.lean`) and certificate checker (`lean/CatchUp/Earlier/CertificateChecker.lean`); its cryptid package (the Turing machine below) is not. Its written research (`results/`, `docs/`, the CU-L ledger) is migrated as claims C90–C103, ideas I20–I22 and additions to earlier claims (2026-11-05). Also: a packed C++ solver (draws, every opening, N = 23, 24, 27, 28, 31, 32); a two-buffer controller and shifted-tail packages (tools); a 388,819,712-state Turing machine (cryptid, not ported) that halts iff the conjecture fails, resting on `Search.halts_iff_not_conjecture` (in our build). Its native certification of every N ≤ 28 (CU-L002, `ofReduceBool`) is outside our Trust rule. Reported, artifact lost: CU-L007/008 (a counterexample needs N ≥ 31), L009, L012, L014, L015, L039; L011 is recovered as CU-R001, a verified theorem (C90).
- Solvers agreeing with our E1–E3: [t1merickson/catchup-exact](https://github.com/t1merickson/catchup-exact) (C, N ≤ 28, cross-checked, no proofs), [Kuberwastaken/c5-k4](https://github.com/Kuberwastaken/c5-k4) (draws at N = 23, 24), [aisaksen/catch-up](https://github.com/aisaksen/catch-up) (the inventors' code, N ≤ 19, plus game-tree statistics).
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- Original paper ([MPRA 108784](https://mpra.ub.uni-muenchen.de/108784/); published in *Game & Puzzle Design* 1(2), 38–49, 2015): proves only the parity facts; notes that even-sum sets in general need not draw (multiset {2,2,2,3,3}).
- Endgames with 3–4 numbers left, case analysis: K. C. G. Feng, honors thesis, College of Staten Island 2024 ([pdf](https://www.math.csi.cuny.edu/Undergraduate/HonorsTheses/2024-feng.pdf)).
- No proof of the conjecture anywhere (searched 2026-10-22, 2026-10-26, 2026-10-30, 2026-11-04); partial results only in catch-up-research.
- formal-conjectures issue #4834 proposes adding the normalized position API upstream (open); the conjecture itself is unchanged.
- Other sets and pairing strategies: only catch-up-research. Nothing on two-player differencing or partitioning games with a catch-up turn rule, or on gap bounds for the final margin (searched 2026-10-28; only one-player Karmarkar–Karp differencing and unrelated discrepancy and heap games). The rounds game (C13) resembles Brams's "Behind First, Alternating Order" sports rule (ties alternate there), with no optimal-play results for number picking (searched 2026-11-04). Misleading: a 2024 Brams article ([Open Access Government](https://www.openaccessgovernment.org/article/a-game-that-poses-a-challenge-to-artificial-intelligence/181077/)) says even-sum sets of 2–20 numbers draw; false for arbitrary sets ({1,3} is a first-player win).

## Reading catch-up-research
Their terms in ours: counter = number; support = set; eligible N = even-total N; effective total = d + sum(R); mate = partner; their "C" = our C1. Their canonical pairs start at even numbers, unlike our aligned pairs (start ≡ k mod 2). "Reserve" and "shadow" name several things there (a shadow is a companion position whose value is assumed); our records say which. Their IDs: CU-Lnnn (Aug–Sep ledger), CU-Rnnn (recovered results); cite them with the prefix.

## Working on it
State: [state.md](state.md) (the current work; it may hold unchecked proposals).
Kind: prove. Modules: none.
