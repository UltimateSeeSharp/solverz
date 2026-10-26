# State

- **Stage:** Attack. Main line A7 (you chose B20, 2026-10-22). Overnight session 2026-10-26: [overnight/2026-10-26.md](overnight/2026-10-26.md).

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 35 is a draw, and for even totals with N ≥ 12 every opening move draws. N = 33 and 34 (odd totals) are player-1 wins, only by opening 1 and 2 respectively. N = 31–35 go beyond the published N = 28; N = 33–35 come from one engine (`tiled-cuda`) and are not independently checked.
- **Blueprint** ([blueprint.md](blueprint.md)): goal statement approved. Formalized: L3 (parity law), L6 (`best` by membership). Paper proofs, refuter-checked: L7 (≤ 2 numbers left), L9 (far-apart pairs), L10 (reductions by partner replies), L11 (two pairs). Conjectures: L4, L5 (near-intervals draw), L12 (even blocks {a..a+2p−1} draw at every height; holds for p ≤ 10, a ≤ 80), L13–L17 (high sets: rounds game, greedy bound, always-max, high pair sets draw, rows of high blocks; L13 and L14 have proof drafts with the refuter). Refuted: L8 (all pair sets draw).
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3 set inductions and completeness; O4 peeling the top pair by a local rule; O5 fixed hole bounds; O6 unconditional partner replies; O7 pair structure alone, aligned pairs included; O8 "opening the top four numbers early never helps" as a local lemma; O9 a monotone descent in block height; O10 a tie law for all offset sets (and even-total sets can be player-2 wins).
- **Leads:** the defender can leave the top four numbers for last and still draw, to N = 28 (A6), and along its best play the attacker opens them early only to rescue a lost game. Density matters: sparse high parts act as a fixed final payoff, and low change of about twice their smallest number cures them, without a clean law (log 2026-10-22: low change cures sparse cores). Blocks at any height draw (L12), and high blocks have the exact row t_p. High sets are exactly a "rounds game" on offsets (L13). There every pair set draws at debt p mod 2 (unlike O7 at low heights), and always taking the largest number is a drawing strategy for both players (L15, checked p ≤ 11); proving L15 gives TI for high blocks for every p (L16). L15's proof is done except the phase after a player's unmatched double (log 2026-10-26: the always-max proof splits at Z's first double).

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|

## Next step

B20: finish the paper proof of AM (log 2026-10-26: toward a proof of AM), the phase after Z doubles; then refuter in proof mode, and blueprint nodes for the rounds-game reduction, AM and "high pair sets draw at p mod 2".

## Awaiting review

- **Branch `overnight/2026-10-26`** (not pushed): first two commits are the 2026-10-22 session's uncommitted work, as it proposed (`feat` for the six experiments, `explore` for the records); then one commit per overnight unit. Merge if you agree.
- **Statements to approve:** none (L9–L11 are helper facts).
- **Lean deviations** from the paper proofs. L3: lemma (B) is proved for any fold step with the property, then applied to `best`; the induction runs on n with `R.card = n`; adapted from the refuter's scratch check. L6: `best`'s step is restated as a private `combine` and proved equal case by case; the loss case is derived from the other two. Both: `lake build --wfail` clean, axioms within propext, Classical.choice, Quot.sound. Their statements need your approval only if we report them as results (they are helper facts). L7 formalization (B5) postponed by you.
- **Higher N: parked (nice to have, user 2026-10-22).** `tiled-cuda` with zstd-compressed tiles (7abf1dd) reaches N ≤ 39 in principle (N = 40 doubles row size). Rough guesses, untimed on an idle machine: N = 36 ~10 min in RAM, 37 ~30 min, 38 ~1–1.5 h, 39 ~2–4 h with ~110 GB peak on disk. First step when revived: a clean N = 34–35 timing run, machine claimed and otherwise idle.
- **Solver hazard.** `Solver::position` doesn't check gap ≤ the largest number; a larger gap silently reads another set's entry (documented in `solver/README.md`; the refuter flagged it again). A `debug_assert` in `lib.rs` would catch it; `lib.rs` is an engine file, so it needs your OK.
- `results/values-n27-32.md` repeats its rows for N = 30–32 at the end of the table (harmless; results are never edited).

## Last review

2026-10-26, after 26 log entries (5 since the previous review; overnight).
- A7 main: metric unchanged (paper proofs of TI for p ≤ 2), but B20 is reduced to one lemma: L15, always-max keeps a draw on pair sets (checked p ≤ 11). Its proof is done except the phase after an unmatched double; L13, L14 are with the refuter.
- Cost: 5 units, all on A7; the ideator was called for fresh ideas on B20 (still running).
- No line meets its kill criteria; A1, A5 dead; A2, A3, A4, A6 shelved, nothing new revives them.
- O10 recorded: no tie law for general offset sets; even-total sets can be player-2 wins.
- Literature: Known checked 2026-10-22; the refuter's searches today found nothing new.
- First review in a row without a metric move.
