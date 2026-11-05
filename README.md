# solverz

AI agents attack open problems in mathematics. A result counts only when
it is a Lean 4 proof the computer has checked, so it can be trusted
without trusting the AI or the search code behind it.

## Results

| Date | Problem | Result | Proof |
|---|---|---|---|
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | A (27, 14, 5) signed difference set exists in C₃ × C₉ (open in Gordon's table) | `SignedDifferenceSets.Answer.N68.hasSDS` |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | A (27, 10, 1) signed difference set exists in C₃ × C₉ (open in Gordon's table) | `SignedDifferenceSets.Answer.N62.hasSDS` |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | A (27, 10, 1) signed difference set exists in C₃ × C₃ × C₃ (open in Gordon's table; He–Chen–Ge's construction at m = 1, outside the range their theorem states) | `SignedDifferenceSets.Answer.N61.hasSDS` |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | A (25, 12, 1) signed difference set exists in C₅ × C₅ (open in Gordon's table) | `SignedDifferenceSets.Answer.N49.hasSDS` |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | No (20, 17, 8) signed difference set exists in C₂ × C₁₀ (open in Gordon's table) | `SignedDifferenceSets.Answer.N32.not_hasSDS` |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/results.md) | No (9, 8, 1) signed difference set exists in C₃ × C₃ (open in Gordon's table) | `SignedDifferenceSets.Answer.N3.not_hasSDS` |

## Problems

| Problem | The question | Status |
|---|---|---|
| [Signed difference sets](problems/signed-difference-sets/README.md) | Which ±1 patterns with perfectly flat autocorrelation exist? Settling open entries of Gordon's table. | 6 open entries settled: 4 sets found, 2 proved impossible |
| [Catch-Up](problems/catch-up/README.md) | Is the number game Catch-Up on 1..N always a draw when the total is even? | open; partial results |
| [R(K₃, K₄−e, K₄−e)](problems/ramsey-k3-k4e-k4e/README.md) | Is this three-colour Ramsey number 21 or 22? | open; search engine being built |

All candidate problems, rated: [problems/problems.md](problems/problems.md).

## Why a result can be trusted

- Lean 4 checks every proof: no `sorry`, no `native_decide`, and
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
- A separate agent tries to break each result before it counts.
- Work by others is credited; their results are not listed as ours.

Check it yourself: `lake build --wfail`.

## How it works

A problem is chosen from the rated list and stated in Lean. An attack
loop then searches, conjectures and proves; agents bring fresh ideas or
try to refute results. Details: [CLAUDE.md](CLAUDE.md),
[principles.md](principles.md).

## Run it

1. Install [elan](https://github.com/leanprover/elan) and [Rust](https://rustup.rs).
2. `lake exe cache get` (prebuilt Mathlib).
3. `lake build` and `cargo build --release`.
