# solverz

@README.md

## Trust rules
- A result counts only if Lean checks it. Every `problems/*/lean/` library must build with no `sorry`, no custom `axiom` and no `native_decide` (it trusts the compiler). Confirm with `#print axioms`: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- The user checks that each theorem statement says what the real problem says. Explain every new statement in plain terms; a proof of the wrong statement is worthless.
- Solvers are untrusted. A certificate one emits counts only once a Lean proof checks it.
- Verification is local, no CI: `lake build --wfail` plus `#print axioms`; `cargo test --release`.
- Before committing to a problem, check it isn't already solved: open PRs in formal-conjectures (`tools/survey/freshness.py`), the erdosproblems.com proof-claims page, recent arXiv. The databases lag by weeks.
- Read any downloaded Lean file fully before compiling it; elaboration can run arbitrary code.

## Working on a problem
- Everything lives in `problems/<problem>/` (kebab-case). New problem: `README.md`, `lean/<Problem>.lean` plus a `[[lean_lib]]` with `srcDir` and a `defaultTargets` entry in `lakefile.toml`, and `solver/` (joins the Cargo workspace automatically).
- The problem's `README.md` is its log: every attempt with its outcome, failures included, and why. Keep the root README problem list current.
- Exploratory files go in `problems/<problem>/scratch/` (git-ignored, persists across sessions), never in a session temp folder. Experiments worth keeping become `solver/src/bin/<name>.rs`; their conclusions go in the log.
- Commit curated solver outputs to `results/` with run metadata (date, commit, command, machine, time); keep raw output out of git.

## Lean
- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`). Ask before bumping.
- Import every module in its library root (e.g. `CatchUp.lean`); `lake build` only checks what the roots import.
- Check a module with `lake build <Module>`. `lake env lean` skips the lakefile's `leanOptions`, e.g. `autoImplicit = false`.
- Start each file with a `/-! ... -/` module doc-string; Mathlib's linter warns otherwise.
- After any Mathlib change, run `lake exe cache get` before building, or Lake compiles Mathlib from source (hours).

## This machine
- The Lean toolchain is on F: because C: is short on space: `ELAN_HOME=F:\WIN_DATA\lean\elan`, `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin` on the user PATH. If `lake` isn't found, the shell predates the install; set them in-process. If VS Code offers to install Lean or elan, it was started without these variables: decline, restart VS Code from the Start menu.
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`, `CARGO_HOME=F:\WIN_DATA\rust\cargo`, GNU toolchain (`x86_64-pc-windows-gnu`, bundled linker, no Visual Studio). Defender flagged the GNU-built `rustup-init.exe` as `Bearfoos.A!ml` (heuristic); the checksum-verified MSVC-built installer worked.
- The user runs long downloads in their own terminal.
