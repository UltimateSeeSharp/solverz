# State

- **Stage:** Attack. **No main line**: needs your decision (Awaiting review).

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 35 is a draw, and for even totals with N ≥ 12 every opening move draws. N = 33 and 34 (odd totals) are player-1 wins, only by opening 1 and 2 respectively. N = 31–35 go beyond the published N = 28; N = 33–35 come from one engine (`tiled-cuda`) and are not independently checked.
- **Blueprint** ([blueprint.md](blueprint.md)): goal statement approved. Formalized: L3 (parity law), L6 (`best` by membership). Paper proofs, refuter-checked: L7 (≤ 2 numbers left), L9 (far-apart pairs), L10 (reductions by partner replies), L11 (two pairs). Conjectures: L4, L5 (near-intervals draw), L12 (even blocks {a..a+2p−1} draw at every height; holds for p ≤ 10, a ≤ 80). Refuted: L8 (all pair sets draw).
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3 set inductions and completeness; O4 peeling the top pair by a local rule; O5 fixed hole bounds; O6 unconditional partner replies; O7 pair structure alone, aligned pairs included; O8 "opening the top four numbers early never helps" as a local lemma; O9 a monotone descent in block height.
- **Leads:** the defender can leave the top four numbers for last and still draw, to N = 28 (A6), and along its best play the attacker opens them early only to rescue a lost game. Density matters: sparse high parts act as a fixed final payoff, and low change of about twice their smallest number cures them, without a clean law (log 2026-10-22: low change cures sparse cores). Blocks at any height draw (L12), and high blocks have the exact row t_p.

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|

## Next step

After you choose: B20, prove the row t_p for high blocks (a ≥ a0(p), where every turn takes one or two numbers) on paper, as L9 did for far-apart pairs.

## Awaiting review

- **Choose a main line** (stop rule: every line is dead or shelved). A6 and A7 were opened and shelved this session (O8, O9). Options: (1) B20, a paper proof for high blocks, a sure partial result that leaves a = 1 open; (2) B23, A6's lemma along the defender's play, closer to {1..N} but needs a new idea; (3) a fresh ideator round; (4) pause the problem.
- **Session 2026-10-22 (continued), uncommitted:** experiments `top_reserve.rs`, `block_rows.rs`, `low_change.rs` (plus `pair_sets.rs`, `far_pairs.rs`, `pair_moves.rs` from earlier today), log (nine entries today), lines (A6, A7 added and shelved), blueprint (L12), backlog, obstructions (O8, O9), solver README, this file. Proposed commits: `feat(catch-up)` for the experiments, `explore(catch-up)` for the records.
- **Statements to approve:** none (L9–L11 are helper facts).
- **Lean deviations** from the paper proofs. L3: lemma (B) is proved for any fold step with the property, then applied to `best`; the induction runs on n with `R.card = n`; adapted from the refuter's scratch check. L6: `best`'s step is restated as a private `combine` and proved equal case by case; the loss case is derived from the other two. Both: `lake build --wfail` clean, axioms within propext, Classical.choice, Quot.sound. Their statements need your approval only if we report them as results (they are helper facts). L7 formalization (B5) postponed by you.
- **Higher N: parked (nice to have, user 2026-10-22).** `tiled-cuda` with zstd-compressed tiles (7abf1dd) reaches N ≤ 39 in principle (N = 40 doubles row size). Rough guesses, untimed on an idle machine: N = 36 ~10 min in RAM, 37 ~30 min, 38 ~1–1.5 h, 39 ~2–4 h with ~110 GB peak on disk. First step when revived: a clean N = 34–35 timing run, machine claimed and otherwise idle.
- **Solver hazard.** `Solver::position` doesn't check gap ≤ the largest number; a larger gap silently reads another set's entry (documented in `solver/README.md`; the refuter flagged it again). A `debug_assert` in `lib.rs` would catch it; `lib.rs` is an engine file, so it needs your OK.
- `results/values-n27-32.md` repeats its rows for N = 30–32 at the end of the table (harmless; results are never edited).

## Last review

2026-10-22, after 21 log entries (5 since the previous review).
- A6 (new, from the ideator): metric moved, Γ_N drawn 24 → 28 (two engines); shelved because Lemma A fails at reachable positions (O8).
- A7 (new): TI holds for p ≤ 10, a ≤ 80, but the band shrinks at {2,3,4,5} (O9); shelved.
- A4 stays shelved: low change cures O7's cores, but with no clean law (B22).
- A5 dead (O7, aligned pairs too); A1 dead; A2, A3 shelved.
- No main line remains: stopped for your decision. The ideator was called for this cycle; its ideas are all tested except the margin tool (B21).
- Literature (Known) checked today; no literature unit due.
