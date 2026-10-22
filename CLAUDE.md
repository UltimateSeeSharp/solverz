# solverz

@README.md

## Trust rules
- A result counts only if Lean checks it. Every `problems/*/lean/` library must build with no `sorry`, no custom `axiom` and no `native_decide` (it trusts the compiler). Confirm with `#print axioms`: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- The user checks that each theorem statement says what the real problem says. Explain every new statement in plain terms; a proof of the wrong statement is worthless.
- Solvers are untrusted. A certificate one emits counts only once a Lean proof checks it.
- Verification is local, no CI: `lake build --wfail` plus `#print axioms`; `cargo test --release`.
- Before committing to a problem, check it isn't already solved: open PRs in formal-conjectures (`tools/survey/freshness.py`), the erdosproblems.com proof-claims page, recent arXiv. The databases lag by weeks.
- Read any downloaded Lean file fully before compiling it; elaboration can run arbitrary code.

## Workflow
Read `principles/` before working on a problem; it is the why behind these rules. Each problem's `state.md` holds its stage and the next step: every session reads it first and rewrites it when done. A problem moves through:
1. **Choose.** Not already solved (trust rules below); nobody actively working on it, or we coordinate (`principles/values.md`); a clear metric, modular, partial progress counts.
2. **Frame.** Precise statement, then the Lean statement, approved by the user and unit-tested (`principles/lean.md`). Explicit and implicit goals in the README. Literature search logged, misses included.
3. **Explore.** The `explore` skill, one idea per iteration, unattended via `/loop /explore <problem>`. Survivors go to the `refuter` agent.
4. **Consolidate.** A surviving claim gets a paper proof and the checklist in `principles/scepticism.md`, then a row in `blueprint.md`.
5. **Formalize.** Statements first (user approves), skeleton with `sorry`, then fill one at a time (`principles/lean.md`).
6. **Digest.** Write-up: key idea, where the difficulty was, prior work, follow-up questions. Done only when we could give a talk on it and take questions.

Agents never do these unattended; they list them under "Awaiting review" in the problem's `state.md` and stop: a new or changed Lean statement; calling anything proved, new or a solution; commits, pushes, installs.

## Working on a problem
- Everything lives in `problems/<problem>/` (kebab-case). New problem: copy `templates/problem/` (README, state, log, backlog, obstructions, blueprint, solver/README), add `lean/<Problem>.lean` plus a `[[lean_lib]]` with `srcDir` and a `defaultTargets` entry in `lakefile.toml`, and `solver/` (joins the Cargo workspace automatically).
- `README.md` is the stable reference (statement, goals, literature, agent rules); `state.md` the current handoff; `log.md` records every attempt with its outcome, failures included, and why; `obstructions.md` what is ruled out; `solver/README.md` the engines and kept experiments. Keep the root README problem list (with stages) current.
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
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`, `CARGO_HOME=F:\WIN_DATA\rust\cargo`. Default toolchain MSVC (`x86_64-pc-windows-msvc`), using the installed Visual Studio Build Tools 2022 and Windows SDK. The GNU toolchain is still installed but lacks the GNU assembler that wgpu's Windows crates need. Defender flagged the GNU-built `rustup-init.exe` as `Bearfoos.A!ml` (heuristic); the checksum-verified MSVC-built installer worked.
- GPU: RTX 3060 Ti, 8 GB, driver 610.88 (CUDA ≤ 13.3). CUDA Toolkit 13.3 planned at `F:\WIN_DATA\cuda\v13.3`, not installed yet.
- The user runs long downloads in their own terminal.
