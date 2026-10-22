# solverz

AI-assisted attacks on open math problems, with every claimed result machine-checked in Lean 4.

A full proof of an open problem would be extraordinary. Realistic wins are machine-checked partial results and write-ups of failed ideas. Lean checks proofs but doesn't find them; its job is to keep the AI honest.

## Layout

One folder per problem; one Lean project (one Mathlib) and one Rust workspace at the root point into them.

| Path | Contents | Trusted? |
|---|---|---|
| `problems/<problem>/README.md` | Stable reference: statement, goals, literature, agent rules | No |
| `problems/<problem>/state.md` | Current stage, results, open threads, next step: the handoff between sessions | No |
| `problems/<problem>/log.md`, `backlog.md`, `obstructions.md`, `blueprint.md` | Every attempt (failures included), idea queue, ruled-out approaches, lemmas toward a proof | No |
| `problems/<problem>/lean/` | Lean library `<Problem>` (Mathlib) | Yes, if it builds with no `sorry` or custom `axiom` |
| `problems/<problem>/solver/` | Rust crate: search/compute code; kept experiments in `src/bin/`; catalog in its `README.md` | No |
| `problems/<problem>/results/` | Curated solver outputs with run metadata | No |
| `problems/<problem>/scratch/` | Playground, git-ignored | No |
| `principles/` | How we work: problem-solving heuristics, scepticism, AI use, Lean, values; distilled from Tao and others, with sources | No |
| `templates/problem/` | Starting files for a new problem: README, state, log, backlog, obstructions, blueprint, solver/README | No |
| `.claude/` | `explore` skill (one research-loop iteration) and `refuter` agent | No |
| `tools/survey/` | Problem-finding pipeline (Python, stdlib only) and its findings | No |

Computations may produce certificates; a certificate counts only once a Lean proof checks it.

## Setup

1. Install [elan](https://github.com/leanprover/elan), the VS Code "Lean 4" extension and [Rust](https://rustup.rs).
2. `lake exe cache get` downloads prebuilt Mathlib instead of compiling it from source (hours).
3. `lake build` and `cargo build --release`

## Verify

- `lake build --wfail` fails on any `sorry` (Lean reports it as a warning). `#print axioms` on each main theorem must list only `propext`, `Classical.choice`, `Quot.sound`.
- `cargo test --release` runs every solver's tests.

## Problems

| Problem | Stage | State |
|---|---|---|
| [Catch-Up conjecture](problems/catch-up/README.md): optimal play on {1..N} is a draw when 1 + … + N is even | Explore | [state.md](problems/catch-up/state.md) |
| [Collatz](problems/collatz/README.md) | Shelved: very unlikely to fall | — |

- **Choosing a target**: surveys of [Erdős problems](tools/survey/erdos.md) and [other formal-conjectures collections](tools/survey/collections.md).
