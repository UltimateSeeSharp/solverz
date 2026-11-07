# solverz

AI agents attack open problems in mathematics. A result counts only when
it is a Lean 4 proof the computer has checked, so it can be trusted
without trusting the AI or the search code behind it.

## Solutions

| Date | Problem | Solution | Proof | Paper |
|---|---|---|---|---|
| 2026-11-07 | [Signed difference sets](problems/signed-difference-sets/README.md) | 16,095 more open entries of Gordon's table settled: 46 sets found, 16,049 proved impossible by 19 Lean-checked rules | [solutions.md](problems/signed-difference-sets/solutions.md) | — |
| 2026-11-05 | [Signed difference sets](problems/signed-difference-sets/README.md) | 6 open entries of Gordon's table settled: 4 sets found, 2 proved impossible | [solutions.md](problems/signed-difference-sets/solutions.md) | — |

## Problems

| Problem | The question | Status |
|---|---|---|
| [Signed difference sets](problems/signed-difference-sets/README.md) | Which ±1 patterns with perfectly flat autocorrelation exist? Settling open entries of Gordon's table. | 16,101 open entries settled: 50 sets found, 16,051 proved impossible; 91% of Gordon's table settled, counting results from the literature |
| [Catch-Up](problems/catch-up/README.md) | Is the number game Catch-Up on 1..N always a draw when the total is even? | open; partial results |
| [R(K₃, K₄−e, K₄−e)](problems/ramsey-k3-k4e-k4e/README.md) | Is this three-colour Ramsey number 21 or 22? | open; search engine being built |

All candidate problems, rated: [problems/problems.md](problems/problems.md).

## Why a result can be trusted

- Lean 4 checks every proof: no `sorry`, no `native_decide`, and
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
- A separate agent tries to break each result before it counts.
- Work by others is credited; their results are not listed as ours.

Check it yourself (Lean 4 and Mathlib v4.35.0), from the repo root:

```
lake exe cache get                         # prebuilt Mathlib, once
lake build --wfail SignedDifferenceSets    # one problem's library
```

A fresh build takes hours and much RAM; each problem's README says what it needs.

## How it works

A problem is chosen from the rated list and stated in Lean. An attack
loop then searches, conjectures and proves; agents bring fresh ideas or
try to refute results. Details: [CLAUDE.md](CLAUDE.md),
[principles.md](principles.md).

## Run it

1. Install [elan](https://github.com/leanprover/elan) and [Rust](https://rustup.rs).
2. `lake exe cache get` (prebuilt Mathlib).
3. `lake build` and `cargo build --release`.

## User skills

In Claude Code, from the repo folder:
- `/choose`: pick a new problem and set it up.
- `/solve <problem>`: work on a problem (its folder name), until you stop it (Esc).
- `/maintain`: work on the repo itself (workflow, skills, templates); never
  inside `/solve`.

## License

- Code and Lean proofs: [Apache-2.0](LICENSE).
- Data and text (problem tables, objects, documentation, papers): [CC BY 4.0](LICENSE-CC-BY-4.0.txt).
- Imported files keep their own license and notice, next to them (e.g.
  `problems/catch-up/lean/CatchUp/BoCowgill/`); data from others is credited in the problem's
  `NOTICE.md` (e.g. [Gordon's SDS data](problems/signed-difference-sets/NOTICE.md)).
