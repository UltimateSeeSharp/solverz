# State

**Focus.** R4 (P1 to the first set, every open Instance with v ≤ 40): sets found for N49, N61, N62, N67, N68, N73 (O6–O11), being checked in Lean (`Answer/N<id>`); none for N30, N89, N90 (no Lean proof yet).
**Next step.** Record R4 and the found sets once Lean checks them; then a fast Lean checker for non-existence (contraction with a verified vector search; exhaustion beyond v ≈ 12), so N30, N89, N90 and the contraction kills can be proved.
**Running.**
- Refuter on N3, N32, F2, F3 (report: `scratch/refuter/report-N3-N32-F2-F3.md`).
- R4: `target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10` at fc100bc, below-normal priority; output `scratch/r4.out`.
- Lean: `lake build --wfail` of `Answer/N49, N61, N62, N67, N68, N73`.

## Needs the user
- Approve the goal: `IsSDS k λ D` (D marks exactly k elements; for every g ≠ 0, Σₓ D(x)·D(x + g) = λ) and `HasSDS G k λ` (some such D on G), settled per Instance as `HasSDS G k λ` or its negation, with G the product of `ZMod` over the key's invariant factors. Tests pass (`Tests/Statement.lean`); refuter SURVIVES (`scratch/refuter-goal.md`: matches Gordon's definition and `sds.json` keys; a known (18, 13, 4) set in C₃ × C₆ passes). Does this say what we mean?
