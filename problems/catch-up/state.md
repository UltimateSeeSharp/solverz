# State

- **Stage:** Attack.

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 35 is a draw, and for even totals with N ≥ 12 every opening move draws. N = 33 and 34 (odd totals) are player-1 wins, only by opening 1 and 2 respectively. N = 31–35 go beyond the published N = 28; N = 33–35 come from one engine (`tiled-cuda`) and are not independently checked.
- **Blueprint** ([blueprint.md](blueprint.md)): goal statement approved. Formalized: L3 (parity law: a drawn position has an even total of scores and numbers left, `lean/CatchUp/Parity.lean`) and L6 (`best` is decided by which outcomes occur, so move order doesn't matter, `lean/CatchUp/Best.lean`). L7 (exact values with ≤ 2 numbers left) has a refuter-checked paper proof. L4 (sets {1..m} minus a few numbers below m still draw, checked to m = 30 with up to 6 holes) and L5 (those positions also draw at moderate gaps) are conjectures with refuter-checked evidence.
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3 set inductions and completeness; O4 peeling the top pair by a local rule (A1 dead); O5 keeping a fixed number of holes under drawing play; O6 always answering with the partner.
- **Leads:** interval positions draw in a middle band of gaps (log 2026-10-22: interval rows). Drawing play looks like pairing {1,2}, {3,4}, …: the defender mostly answers with the partner, but its defects grow like N/6 and it must sometimes refuse the partner. When to refuse has no cheap rule: it depends on where the opponent's new deficit falls in its draw band (log 2026-10-22: no simple rule). A2 is close to its kill criterion; a new idea is needed for the main line.

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|

## Next step

B5: formalize L7 (endgames with ≤ 2 numbers; paper proof, statement shape in its blueprint section) in `lean/CatchUp/Endgame.lean`, via a membership form of `valueAux` built on L6.

## Awaiting review

- **Lean deviations** from the paper proofs. L3: lemma (B) is proved for any fold step with the property, then applied to `best`; the induction runs on n with `R.card = n`; adapted from the refuter's scratch check. L6: `best`'s step is restated as a private `combine` and proved equal case by case; the loss case is derived from the other two. Both: `lake build --wfail` clean, axioms within propext, Classical.choice, Quot.sound. Their statements need your approval only if we report them as results (they are helper facts).
- **Main line nearly exhausted.** A2 (an invariant class of positions) has failed with four hole measures and with pairing strategies (O5, O6); A1 is dead, A3 and A4 are shelved. If you have an idea for a new line, now is a good time; otherwise the next review proposes new lines.
- **Higher N: parked (nice to have, user 2026-10-22).** `tiled-cuda` with zstd-compressed tiles (7abf1dd) reaches N ≤ 39 in principle (N = 40 doubles row size). Rough guesses, untimed on an idle machine: N = 36 ~10 min in RAM, 37 ~30 min, 38 ~1–1.5 h, 39 ~2–4 h with ~110 GB peak on disk. First step when revived: a clean N = 34–35 timing run, machine claimed and otherwise idle.
- **Solver hazard.** `Solver::position` doesn't check gap ≤ the largest number; a larger gap silently reads another set's entry (documented in `solver/README.md`). A `debug_assert` in `lib.rs` would catch it; `lib.rs` is an engine file, so it needs your OK.
- `results/values-n27-32.md` repeats its rows for N = 30–32 at the end of the table (harmless; results are never edited).

## Last review

2026-10-22, after 10 log entries.
- A1 dead (O4): adding a top pair doesn't change values by a local rule.
- A2 main; metric moved: a sound candidate class (L4, L5), then its closure tested and failing for fixed hole bounds (O5) and for unconditional pairing (O6). Its kill criterion is close: four hole measures and pairing all fail more as N grows. One more candidate (B9 or B2) before shelving.
- A3 shelved: fixed and pair-repairing rules lose by N = 4–7; a forced partner reply loses from N = 11.
- A4 shelved; L4 suggests "few holes" as its density notion, but no set induction.
- Literature (Known) checked today; no literature unit due.
