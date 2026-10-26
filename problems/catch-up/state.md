# State

- **Stage:** Attack. Main line A7 (you chose B20, 2026-10-22). Overnight session 2026-10-26: [overnight/2026-10-26.md](overnight/2026-10-26.md).

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 35 is a draw, and for even totals with N ≥ 12 every opening move draws. N = 33 and 34 (odd totals) are player-1 wins, only by opening 1 and 2 respectively. N = 31–35 go beyond the published N = 28; N = 33–35 come from one engine (`tiled-cuda`) and are not independently checked.
- **Blueprint** ([blueprint.md](blueprint.md)): goal statement approved. Formalized: L3 (parity law), L6 (`best` by membership), L13 (high sets are the rounds game). Paper proofs, refuter-checked: L7 (≤ 2 numbers left), L9 (far-apart pairs), L10 (reductions by partner replies), L11 (two pairs), L14 (greedy bound), L15 (always-max on pair sets), L16 (pair sets above their sum draw: TI for blocks with a > 1 + p(2p−1), every p). Conjectures: L4, L5 (near-intervals draw), L12 (even blocks {a..a+2p−1} draw at every height; holds for p ≤ 10, a ≤ 80), L17 (rows of high blocks). Refuted: L8 (all pair sets draw).
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3 set inductions and completeness; O4 peeling the top pair by a local rule; O5 fixed hole bounds; O6 unconditional partner replies; O7 pair structure alone, aligned pairs included; O8 "opening the top four numbers early never helps" as a local lemma; O9 a monotone descent in block height; O10 a tie law for all offset sets (and even-total sets can be player-2 wins).
- **Leads:** the defender can leave the top four numbers for last and still draw, to N = 28 (A6), and along its best play the attacker opens them early only to rescue a lost game. Density matters: sparse high parts act as a fixed final payoff, and low change of about twice their smallest number cures them, without a clean law (log 2026-10-22: low change cures sparse cores). Blocks at any height draw (L12), and high blocks have the exact row t_p. High sets are exactly a "rounds game" on offsets (L13). There every pair set draws at debt p mod 2 (unlike O7 at low heights), and always taking the largest number is a drawing strategy for both players (L15), which gives TI for high blocks for every p (L16); both are refuter-checked paper proofs (log 2026-10-26: the always-max lemma survives proof mode). One exception to always-max, never answering with an exact tie (AM+T), is optimal on every row of high blocks and on pair sets at debts 0 and 1 (checked p ≤ 12; log 2026-10-26: avoiding exact ties gives every row of high blocks).

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|

## Next step

B26: prove L19 (blueprint): an invariant along AM+T play, using where Y's holes are, that gives L18's condition wherever Y moves.

## Awaiting review

- **Branch `overnight/2026-10-26`** (not pushed): first two commits are the 2026-10-22 session's uncommitted work, as it proposed (`feat` for the six experiments, `explore` for the records); then one commit per overnight unit. Merge if you agree.
- **Statements to approve:** none yet. New paper proof, refuter-checked, not formalized: L16, even blocks {a..a+2p−1} draw for every p once a > 1 + p(2p−1) (from L13 and L15). It is not a solution of the problem and is not reported anywhere. If you want it reported as a partial result, its Lean statement goes through `audit-statement` and your approval; formalizing L13 and L15 needs no approval (helper facts).
- **Lean deviations** from the paper proofs. L13 (2026-10-26, `CatchUp.valueAux_map_add` in `CatchUp/Rounds.lean`): `roundsValue` also gives odd offset sets a value (the mover wins when no answer is left; never used by L13); s stays universally quantified in the induction instead of "V depends only on the deficit"; the early-loss rule is handled at the other player's node, where it fires only with one number left. L3: lemma (B) is proved for any fold step with the property, then applied to `best`; the induction runs on n with `R.card = n`; adapted from the refuter's scratch check. L6: `best`'s step is restated as a private `combine` and proved equal case by case; the loss case is derived from the other two. Both: `lake build --wfail` clean, axioms within propext, Classical.choice, Quot.sound. Their statements need your approval only if we report them as results (they are helper facts). L7 formalization (B5) postponed by you.
- **Higher N: parked (nice to have, user 2026-10-22).** `tiled-cuda` with zstd-compressed tiles (7abf1dd) reaches N ≤ 39 in principle (N = 40 doubles row size). Rough guesses, untimed on an idle machine: N = 36 ~10 min in RAM, 37 ~30 min, 38 ~1–1.5 h, 39 ~2–4 h with ~110 GB peak on disk. First step when revived: a clean N = 34–35 timing run, machine claimed and otherwise idle.
- **Solver hazard.** `Solver::position` doesn't check gap ≤ the largest number; a larger gap silently reads another set's entry (documented in `solver/README.md`; the refuter flagged it again). A `debug_assert` in `lib.rs` would catch it; `lib.rs` is an engine file, so it needs your OK.
- `results/values-n27-32.md` repeats its rows for N = 30–32 at the end of the table (harmless; results are never edited).

## Last review

2026-10-26, after 31 log entries (5 since the previous review; overnight).
- A7 main: metric moved. TI has a paper proof for every p once a > 1 + p(2p−1) (L16, from L13 and L15, each refuter-checked in proof mode). Cost: 5 units, one of them the ideator's.
- Also on A7: one rule, AM+T, is optimal on every row of high blocks and on pair sets at debts 0 and 1 (checked p ≤ 12); toward its proof, a potential step lemma (L18) is drafted.
- No line meets its kill criteria; A1, A5 dead; A2, A3, A4, A6 shelved, nothing new revives them. A7 stays main: it is the only line whose metric moves.
- Backlog within 10 items per line. Known checked 2026-10-22 and again by the refuter today (nothing new): no literature unit due.
- Ideator called for this review on the descent from high blocks to a = 1 (B27, O9); its ideas go to the backlog when it reports.
