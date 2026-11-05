# State

**Focus.** Set up, waiting for the goal's approval and for "attack signed-difference-sets".
**Next step.** On attack: refuter on S1, S2 (`CaseS1`, `CaseS2`, Lean-checked) and F2, F3; then the Lean side of the 13 contraction kills (`scratch/contract40.out`, needs a pruned vector check, the plain `decide` space is too big), and R3 (`r3_open_cases`) on the 41 cases in `scratch/r3-cases.txt`.
**Running.** nothing.

Done ahead of the attack (setup day, 2026-11-05; scratch files are not records yet):
- S1 (9, 8, 1) in C₃ × C₃ and S2 (20, 17, 8) in C₂ × C₁₀: no SDS, proved in Lean (in the library root; `lake build --wfail` passes; `#print axioms`: propext, Classical.choice, Quot.sound); refuter pending.
- Gordon's Open keys with v ≤ 40: 91; He–Wu's four criteria, reimplemented (`scratch/hewu.py`), leave 55; contraction to quotients (F3, `scratch/contract2.py`) kills 13 of those, S2 among them.

## Needs the user
- Approve the goal: `IsSDS k λ D` (D marks exactly k elements; for every g ≠ 0, Σₓ D(x)·D(x + g) = λ) and `HasSDS G k λ` (some such D on G), settled per case as `HasSDS G k λ` or its negation, with G the product of `ZMod` over the table key's invariant factors. Tests pass (`Tests/Statement.lean`); refuter SURVIVES (`scratch/refuter-goal.md`: matches Gordon's definition and `sds.json` keys; a known (18, 13, 4) set in C₃ × C₆ passes). Does this say what we mean?
- Import Gordon's data (github.com/dmgordo/signed-difference-sets, `sds.json`) and He–Wu's open-case script (github.com/zhiwenhe94/sds-open-case-verification) for the full open-case list; the v ≤ 40 keys were read online (`scratch/open40.txt`).
