# State

**Focus.** Research stopped by the user 2026-11-05 after E4 (`experiments/E4.md`): 6 found sets Lean-checked, 9 more found but unchecked, 16 Instances exhausted without a Lean proof, 22 not reached.
**Next step.** IDs migrated 2026-11-05: runs R<n> are now experiments E<n> (`experiments/`), Results T<n> are now Solutions Z<n>; the worktree's scratch files still use the old IDs, and its uncommitted `bin/r5_contraction.rs` still says R5 in its doc comment: make it E5. On the next attack: save E4's 9 unchecked sets as objects and check them in Lean (`solver/answer.py`), each checked against the known constructions first; then a fast Lean checker for non-existence (contraction with a verified vector search; exhaustion beyond v ≈ 12) for E4's 16 exhausted Instances. Uncommitted in the worktree: the contraction engine for E5 (`solver/src/contraction.rs`, `instances.rs`, `bin/r5_contraction.rs`, two `mod` lines in `lib.rs`); its first run stopped in validation with no output, so it has not been checked.
**Running.** nothing.

## Needs the user
- Findings to bring to the user: N63319, N14604, N31832, N14471 are settled in Gordon or He–Chen–Ge, so `instances.csv` lists them as open wrongly.
