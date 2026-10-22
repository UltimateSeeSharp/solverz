# Blueprint

Status and Approved: `CLAUDE.md`, Workflow.

| ID | Name | Statement | Uses | Line | Lean | Status | Approved |
|---|---|---|---|---|---|---|---|
| L1 | Collatz conjecture | Every n ≥ 1 reaches 1 | — | all | — | conjecture | — |
| L2 | Climb lemma | If n = 2^a·m − 1 with m odd, T makes exactly a odd steps in a row, reaching 3^a·m − 1 | — | A1 | — | conjecture | — |

## L1 Collatz conjecture
**Proof.** Open.
**Evidence.** —

## L2 Climb lemma
**Proof.** For a ≥ 1, 2^a·m − 1 is odd, and T(2^a·m − 1) = (3·2^a·m − 2)/2 = 3·2^(a−1)·m − 1, which has the same form with a − 1 and 3m. After a steps the value is 3^a·m − 1, which is even since 3^a·m is odd.
**Evidence.** Consequence: descent certificates need unbounded look-ahead, and the limit of these climbs is the 2-adic −1 (O2). Refuter not run on the proof.
