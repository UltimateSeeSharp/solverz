# solverz

AI-assisted attacks on open math problems, with every claimed result machine-checked in Lean 4.

A full proof of an open problem would be extraordinary. Realistic wins are machine-checked partial results and write-ups of failed ideas. Lean checks proofs but doesn't find them; its job is to keep the AI honest.

## Layout

| Path | Contents | Trusted? |
|---|---|---|
| `Solverz/<Problem>/` | Lean library (Mathlib), one folder per problem | Yes, if it builds with no `sorry` or custom `axiom` |
| `Solverz/Common/` | Lean lemmas shared across problems | Same |
| `experiments/<problem>/` | Python (uv) and Rust search/compute code | No, exploration only |
| `notes/<problem>.md` | Idea log, including failed attempts and why | No |

Experiments may produce certificates; a certificate counts only once a Lean proof checks it.

## Setup

1. Install [elan](https://github.com/leanprover/elan) and the VS Code "Lean 4" extension.
2. `lake exe cache get` downloads prebuilt Mathlib instead of compiling it from source (hours).
3. `lake build`

## Verify

`lake build --wfail` fails on any `sorry` (Lean reports it as a warning). `#print axioms` on each main theorem must list only `propext`, `Classical.choice`, `Quot.sound`.

## Problems

- **Choosing a target**: Erdős problems surveyed, see [notes/erdos-survey.md](notes/erdos-survey.md).
- **Collatz (3n+1)**: shelved; very unlikely to fall. Ideas: [notes/collatz.md](notes/collatz.md).
