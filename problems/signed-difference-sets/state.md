# State

**Focus.** Research stopped by the user 2026-11-05 after R4 (`runs/R4.md`): 6 found sets Lean-checked, 9 more found but unchecked, 16 Instances exhausted without a Lean proof, 22 not reached.
**Next step.** On the next attack: save R4's 9 unchecked sets as objects and check them in Lean (`solver/answer.py`), each checked against the known constructions first; then a fast Lean checker for non-existence (contraction with a verified vector search; exhaustion beyond v ≈ 12) for R4's 16 exhausted Instances. Uncommitted in the worktree: the contraction engine for R5 (`solver/src/contraction.rs`, `instances.rs`, `bin/r5_contraction.rs`, two `mod` lines in `lib.rs`); its first run stopped in validation with no output, so it has not been checked.
**Running.** nothing.

## Needs the user
- Record T3–T6, approved 2026-11-05: N49 (25,12,1) in C₅ × C₅; N61 (27,10,1) in C₃³ (origin: first stated and Lean-checked here, He–Chen–Ge's construction at m = 1, outside the range their theorem states); N62 (27,10,1) in C₃ × C₉; N68 (27,14,5) in C₃ × C₉. Lean-checked, refuter SURVIVES (`scratch/refuter/r4-report.md`). Goes into `results.md` and the README after the merge.
- Findings to bring to the user after T3–T6: N67, N73 are in Gordon 2022 (Prop 2.3, Thm 4.1), marked Open in his database by mistake; N63319, N14604, N31832, N14471 are settled in Gordon or He–Chen–Ge, so `instances.csv` lists them as open wrongly.
