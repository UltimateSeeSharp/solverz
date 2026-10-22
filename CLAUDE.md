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
Read `principles/` before working on a problem; it is the why behind these rules. Each problem's `state.md` holds its stage, loop status and next step: every session reads it first and rewrites it when done. A session claims the thread it works on under "Claims" there; a claim older than 12 hours is stale and may be taken over.

**Tools.** `choose`: survey, shortlist and set up a new problem. `explore`: one iteration on one line of attack in one mode (survey, conjecture, search, prove, literature); run unattended with `/loop /explore <problem>`. `review`: every 5th iteration, or by hand; scores and reallocates lines, prunes, reports. `audit-statement`: prepares every Lean statement for the user's approval. `formalize`: turns an approved node's paper proof into Lean. `digest`: the write-up that takes a node to `digested`. `refuter` agent: attacks claims, proofs and statements.

**Lines of attack** (`lines.md`) steer the work: each is a route to the goal with its reduction, a metric, a budget and kill criteria; exactly one is `main`. Progress means a line's metric moved.

**Promotion ladder** for blueprint nodes; only the named party advances a step:
`observed` (seen in data) → `computed` (holds in every case up to a bound; code checked against known values) → `survived` (refuter, claim mode) → `paper proof` (its section in `blueprint.md`, checklist in `principles/scepticism.md`) → `proof survived` (refuter, proof mode) → `statement approved` (`audit-statement`, then **the user**) → `formalized` (`lake build --wfail`, clean `#print axioms`, deviations listed) → `digested` (write-up: key idea, where the difficulty was, prior work, follow-up questions; AI-reviewed line by line; **the user** confirms it explains the result).

**Stages** of a problem, with exit criteria:
1. **Choose** → Frame: not already solved (trust rules); nobody actively working on it, or we coordinate (`principles/values.md`); a clear metric, modular, partial progress counts, answers cheap to check.
2. **Frame** → Explore: the goal statement audited and approved; explicit and implicit goals in the README; literature logged, misses included; at least two lines in `lines.md`.
3. **Explore** → Consolidate: every node of the main line's blueprint at `survived` or better.
4. **Consolidate** → Formalize: every main-line node at `proof survived`.
5. **Formalize** → Digest: the goal node `formalized`.
6. **Digest** → done: the goal node `digested`.

**Stop rules.** The loop sets **Loop** to stopped in `state.md`, says why under "Awaiting review", and waits for the user when: the main line is blocked on a user decision and no other line has budget; a main-line node reaches `proof survived` (claimed breakthrough); or two reviews in a row saw no metric move.

**Never unattended**, always via "Awaiting review": approving a Lean statement; calling anything proved, new or a solution; commits, pushes, installs.

## Working on a problem
- Everything lives in `problems/<problem>/`. New problem: copy `templates/problem/` (README, state, lines, log, backlog, obstructions, blueprint, solver/README), add `lean/<Problem>.lean` plus a `[[lean_lib]]` with `srcDir` and a `defaultTargets` entry in `lakefile.toml`, and `solver/` (joins the Cargo workspace automatically).
- Each kind of information has one home; everything else links to it. In a problem: statement, goals, literature, agent rules → `README.md`; current position → `state.md` (a summary with links); lines of attack → `lines.md`; ideas → `backlog.md`; ruled out → `obstructions.md`; lemmas → `blueprint.md` (+ `lean/`); our computations → `results/`; every attempt, failures included → `log.md`; engines and kept experiments → `solver/README.md`; write-ups → `digest/`. Repo-wide: rules and conventions → this file; their why → `principles/`; procedures → skills, which reference rules instead of restating them; file shapes → `templates/`; problem surveys and shortlists → `research/selection/`; overview and the problem list with stages → root `README.md` (keep it current).
- Exploratory files go in `problems/<problem>/scratch/` (git-ignored, persists across sessions), never in a session temp folder. Experiments worth keeping become `solver/src/bin/<name>.rs`; their conclusions go in the log.

## Conventions
- **Problem folders:** kebab-case (`catch-up`). The problem's Lean library is the same words in UpperCamelCase (`CatchUp`); its solver crate keeps the folder name.
- **Lean files:** UpperCamelCase, one file per topic (`CatchUp/Parity.lean`); `Statement.lean` holds only the approved statement.
- **Lean names:** [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html): theorems snake_case (`parity_law`), value-computing definitions lowerCamelCase (`valueAux`), types and `Prop` definitions UpperCamelCase (`Conjecture`), all in the problem's namespace (`CatchUp.parity_law`).
- **Rust names:** [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html): modules, functions and files snake_case, types UpperCamelCase. An experiment binary is named after the question it answers (`quad_step`).
- **Blueprint:** [leanblueprint](https://github.com/PatrickMassot/leanblueprint) style in Markdown: an index table (ID, Name, Statement, Uses, Line, Lean, Status) and one section per lemma with its paper proof and evidence. Line lists the lines it serves (`A1, A2`); the goal node has `all`.
- **IDs:** lines of attack `A1`…, blueprint lemmas `L1`…, backlog ideas `B1`…, obstructions `O1`…; stable through reordering, never reused. Log entries are referenced by their heading (`<date>: <title>`). Cross-references use IDs ("O1 rules out B4").
- **Scratch:** experiment output is named `<experiment>-<args>.<ext>` (`quad_step-30.md`); agents may keep a working folder (`scratch/refuter/`). Nothing in scratch counts as a result.
- **Dates:** ISO 8601 (`2026-10-22`).
- **Commits:** [Conventional Commits](https://www.conventionalcommits.org) `type(scope): summary`, then a body with what and why. Scope: the problem folder, or the repo area (`principles`, `tools`, `templates`, `workflow`). Types: `feat`, `fix`, `explore` (one loop iteration), `results`, `docs`, `refactor`, `perf`, `test`, `chore`. One logical change per commit, never two problems in one.
- **Log:** every entry has all seven fields of the format in `templates/problem/log.md`, unused ones stated ("not run", "not searched"). Append-only: a mistake gets a new entry naming the one it corrects.
- **Results:** `results/` holds only our own computations (literature values go to the README, debug runs to `scratch/`). One file per run, `results/<quantity>[-<scope>].md`, never edited; a newer run whose scope contains the old one replaces it. Header: Date, Command, Commit, Machine, Runtime, Checked (independent verification, or "unchecked"); where they apply, Inputs (seeds, external data with version or hash), Scope completed (runs cut short), Data (path and SHA-256 of output kept outside git). A search states the exact scope searched and the outcome, including "found nothing". Data a Lean proof reads lives under `lean/`. Other files link to results instead of copying their data; a one-line conclusion is fine.

## Lean
- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`). Ask before bumping.
- Import every module in its library root (e.g. `CatchUp.lean`); `lake build` only checks what the roots import.
- Check a module with `lake build <Module>`. `lake env lean` skips the lakefile's `leanOptions`, e.g. `autoImplicit = false`.
- Start each file with a `/-! ... -/` module doc-string; Mathlib's linter warns otherwise.
- After any Mathlib change, run `lake exe cache get` before building, or Lake compiles Mathlib from source (hours).

## This machine
- The Lean toolchain is on F: because C: is short on space: `ELAN_HOME=F:\WIN_DATA\lean\elan`, `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin` on the user PATH. If `lake` isn't found, the shell predates the install; set them in-process. If VS Code offers to install Lean or elan, it was started without these variables: decline, restart VS Code from the Start menu.
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`, `CARGO_HOME=F:\WIN_DATA\rust\cargo`. Toolchain: MSVC (`x86_64-pc-windows-msvc`) with the installed Visual Studio Build Tools 2022 and Windows SDK.
- GPU: RTX 3060 Ti, 8 GB, driver 610.88 (supports CUDA ≤ 13.3). CUDA Toolkit 13.3 in `C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.3` (`CUDA_PATH`; DLLs in `bin\x64`).
- The user runs every install and download: give them the exact command instead of running it.
