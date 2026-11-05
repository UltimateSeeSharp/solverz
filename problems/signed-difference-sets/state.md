# State

**Focus.** Set up; waiting for the goal's approval and for "attack signed-difference-sets".
**Next step.** On attack: the refuter on N3 and N32 (`Answer/N3`, `Answer/N32`, Lean-checked) and on F2, F3; then the open Instances smallest first (`instances.csv`, 22,457 open).
**Running.** nothing.

## Needs the user
- Approve the goal: `IsSDS k λ D` (D marks exactly k elements; for every g ≠ 0, Σₓ D(x)·D(x + g) = λ) and `HasSDS G k λ` (some such D on G), settled per Instance as `HasSDS G k λ` or its negation, with G the product of `ZMod` over the key's invariant factors. Tests pass (`Tests/Statement.lean`); refuter SURVIVES (`scratch/refuter-goal.md`: matches Gordon's definition and `sds.json` keys; a known (18, 13, 4) set in C₃ × C₆ passes). Does this say what we mean?
