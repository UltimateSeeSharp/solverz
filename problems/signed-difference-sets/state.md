# State

**Focus.** Setup: the goal's audit; the first engine (P1) in Rust, validated on O1–O5.
**Next step.** Write the P1 engine (`solver/src/`), reproduce O1–O5, rerun S1 and S2 as R1; then prove S1 none in Lean (F2, then `decide` over the 2⁸ sign patterns with 0 fixed).
**Running.**
- Refuter on the goal statement (audit step 5), started 2026-11-05; notes in `scratch/refuter-goal.md`.

## Needs the user
- Approve the goal: `IsSDS k λ D` (D marks exactly k elements; for every g ≠ 0, Σₓ D(x)·D(x + g) = λ) and `HasSDS G k λ` (some such D on G), settled per case as `HasSDS G k λ` or its negation. Tests pass (`Tests/Statement.lean`); the refuter's verdict is pending. Does this say what we mean?
- Import Gordon's data (github.com/dmgordo/signed-difference-sets, `sds.json`) and He–Wu's open-case script (github.com/zhiwenhe94/sds-open-case-verification) for the full open-case list; until then we work the cases the triage found.
