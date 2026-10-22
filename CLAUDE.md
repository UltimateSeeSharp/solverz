# solverz

@README.md

## Trust rules
- A result counts only if Lean checks it. Code under `Solverz/` must build with no `sorry`, no custom `axiom` and no `native_decide` (it trusts the compiler). Confirm with `#print axioms`: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- The user checks that each theorem statement says what the real problem says. Explain every new statement in plain terms; a proof of the wrong statement is worthless.
- `experiments/` is untrusted. A certificate it emits counts only once a Lean proof checks it.
- Log every attempt in `notes/<problem>.md`, failures included, with why it failed. Keep the README problem list current.
- Verification is local, no CI: `lake build --wfail` plus `#print axioms`.
- Before committing to a problem, check it isn't already solved: open PRs in formal-conjectures, the erdosproblems.com proof-claims page, recent arXiv. The databases lag by weeks.
- Read any downloaded Lean file fully before compiling it; elaboration can run arbitrary code.

## Lean
- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`). Ask before bumping.
- Import every new module in `Solverz.lean`; `lake build` only checks what it imports.
- Check a file with `lake build Solverz.<Module>`. `lake env lean` skips the lakefile's `leanOptions`, e.g. `autoImplicit = false`.
- Start each file with a `/-! ... -/` module doc-string; Mathlib's linter warns otherwise.
- After any Mathlib change, run `lake exe cache get` before building, or Lake compiles Mathlib from source (hours).

## This machine
- The toolchain is on F: because C: is short on space: `ELAN_HOME=F:\WIN_DATA\lean\elan`, `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin` on the user PATH. If `lake` isn't found, the shell predates the install; set them in-process.
- The user runs long downloads in their own terminal.
