# solverz

AI-assisted attacks on open math problems, with every claimed result machine-checked in Lean 4.

## Layout

| Path | Contents | Trusted? |
|---|---|---|
| `Solverz/` | Lean library (Mathlib), one folder per problem | Yes, if it builds with no `sorry` |
| `experiments/<problem>/` | Python (uv) and Rust search/compute code | No, exploration only |
| `notes/<problem>.md` | Idea log, including failed attempts and why | No |

Experiments may produce certificates; a certificate counts only once a Lean proof checks it.

## Problems

- **Collatz (3n+1)**: not started.
