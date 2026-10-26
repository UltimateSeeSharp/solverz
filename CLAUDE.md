# solverz

@README.md

## Trust rules
- A result counts only if Lean checks it. Every `problems/*/lean/` library must build with no `sorry`, no custom `axiom` and no `native_decide` (it trusts the compiler). Confirm with `#print axioms`: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- The user checks that every statement we report (the goal, and any lemma presented as a result) and the definitions it uses say what the real problem says. Explain each in plain terms; a proof of the wrong statement is worthless. Helper lemmas need no approval: Lean proves them, so a badly stated one can block the proof but not falsify the result.
- Solvers are untrusted. A certificate one emits counts only once a Lean proof checks it.
- Verification is local, no CI: `lake build --wfail` plus `#print axioms`; `cargo test --release`.
- Before committing to a problem, check it isn't already solved: open PRs in formal-conjectures (`tools/survey/freshness.py`), the erdosproblems.com proof-claims page, recent arXiv. The databases lag by weeks.
- Read any downloaded Lean file fully before compiling it; elaboration can run arbitrary code.

## Workflow
Read `principles/` before working on a problem; it is the why behind these rules. Each problem's `state.md` is the handoff: every session reads it and the files it links first, and updates it before ending.

**Stages** of a problem, with exit criteria. A problem can be shelved at any stage (`<stage>, shelved: <reason>`).
1. **Choose** → Frame: not already solved (trust rules); nobody actively working on it, or we coordinate (`principles/values.md`); a clear metric, modular, partial progress counts, answers cheap to check. Survey: `tools/survey/README.md`; shortlists in `research/selection/`; the user picks.
2. **Frame** → Attack: the goal statement audited and approved; explicit and implicit goals in the README; literature logged, misses included; at least two lines in `lines.md`.
3. **Attack** → done: the goal node `formalized`.

**Lines of attack** (`lines.md`): each is a route to the goal with its reduction, a metric and kill criteria; exactly one is `main`. Progress means a line's metric moved.

**Blueprint status** of a node; only the named party advances it:
`conjecture` (stated; its section records the evidence: bounds computed with checked code, refuter verdicts) → `paper proof` (its section holds a proof that passes the checklist in `principles/scepticism.md` and survived the refuter in proof mode) → `formalized` (`lake build --wfail`, clean `#print axioms`, deviations listed).
**Approved**, a separate column: the date **the user** approved the node's Lean statement after the `audit-statement` skill. Required for the goal and any node reported as a result; `—` otherwise.

**Attacking a problem.** First tell the user in one line the mode (normal or overnight) and that it's starting. Repeat until a stop rule fires or the request is done:
1. **Pick** the Next step in `state.md`, else the main line's best backlog item. Skip what is logged, ruled out in `obstructions.md`, or held by a claim. At least one unit in five goes to another line or to an idea unlike anything logged. New ideas come from the `ideator` agent (effort max; sessions run at xhigh): call it for that fifth unit, at each review, and when a line's backlog is empty; add the ideas you keep to `backlog.md` with new IDs.
2. **Work** one unit: compute data, state a conjecture, run a search, prove a node on paper, formalize a `paper proof` node, or answer one literature question. Stay within the README's agent rules.
3. **Refute**: a claim or search result goes to the `refuter` agent in claim mode, a paper proof in proof mode; record its verdict as given. A proof-mode SURVIVES moves the node to `paper proof`.
4. **Record**: one log entry; the line's metric; counterexamples in `obstructions.md`; the backlog (remove the item, add at most two follow-ups); blueprint changes; kept experiments in `solver/README.md`.
5. **Review** once 5 log entries have passed since the last review: score each line (did its metric move, at what cost); kill (`dead`, citing the obstruction) or shelve (reason, and what would revive it) lines that meet their kill criteria, never delete one; choose the main line by evidence, not sunk work; prune the backlog to 10 items per line; if the README's Known was checked over 14 days ago, make a literature unit next, including whether someone announced a solution. Report under "Last review" in `state.md`, in at most 8 plain lines.

**Don't wait.** Run experiments, builds, tests and agents in the background and work on the next unit meanwhile. Limits: at most 3 agents and 1 experiment at a time. Nothing builds on a claim before its verdict.

**Stop rules.** Stop and wait for the user, saying why under "Awaiting review", when: the main line needs a user decision and no other line has work; the goal reaches `paper proof` (claimed solution); or two reviews in a row saw no metric move. Before ending any session, update `state.md` (Where things stand, Next step as one concrete action, Awaiting review) and tell the user in three plain lines what was tried, what came out, what's next.

**Overnight.** "attack <problem>, overnight": no stop rules, no questions, and it runs until the user stops it: never end it on your own; while agents or experiments run, work on another unit. Whatever needs the user goes under "Awaiting review" and work moves to another line or a new `ideator` idea. Update `state.md` and the log after every unit, so a crash or usage limit loses nothing. Keep `problems/<p>/overnight/<date>.md`: a summary at the top, rewritten each unit (what came out, what needs the user), then one line per unit linking its log entry. Commit each unit to branch `overnight/<date>`, never to `main`, never push; the user merges in the morning.

**Never without the user**, always via "Awaiting review": approving a Lean statement; calling anything proved, new or a solution; sharing anything outside the repo; commits, pushes, installs.

**Formalizing** a node needs: status `paper proof`, Approved if it needs approval, and every node it uses formalized. Follow the recipe in `principles/lean.md` (skeleton with `sorry` first). Never edit an approved statement; a missing hypothesis sends it back through `audit-statement`. List every deviation from the paper proof, correct the node's section to match, and put the list under "Awaiting review".

**Sharing** a result outside the repo needs a write-up first, `writeups/<node>.md`: the key idea, where the difficulty was, prior work, AI and tool use, each claim citing its blueprint node, log entry or source. The `refuter` checks its argument in proof mode, it is read against the deviation list, and the user confirms it explains the result.

**Parallel sessions.** Long-running work (a solver run, a GPU job) is listed under "Claims" in `state.md` with the machine resources it holds, and removed when done; other sessions don't start work that collides with it. A claim older than 12 hours is stale. Each session edits only the parts of `state.md` its work changes.

## Working on a problem
- Everything lives in `problems/<problem>/`. New problem: copy `templates/problem/` (README, state, lines, log, backlog, obstructions, blueprint, solver/README), add `lean/<Problem>.lean` plus a `[[lean_lib]]` with `srcDir` and a `defaultTargets` entry in `lakefile.toml`, and `solver/Cargo.toml` at once (every `problems/*/solver` joins the Cargo workspace; one without a `Cargo.toml` breaks every cargo command). Set `state.md` to stage Frame and add the problem to the root README's table.
- Each kind of information has one home; everything else links to it. In a problem: statement, goals, literature, agent rules → `README.md`; current position → `state.md` (a summary with links); lines of attack → `lines.md`; ideas → `backlog.md`; ruled out → `obstructions.md`; lemmas → `blueprint.md` (+ `lean/`); our computations → `results/`; every attempt, failures included → `log.md`; engines and kept experiments → `solver/README.md`; write-ups for sharing → `writeups/`; overnight reports → `overnight/`. Repo-wide: rules and conventions → this file; their why → `principles/`; fixed procedures → skills, which reference rules instead of restating them; file shapes → `templates/`; problem surveys and shortlists → `research/selection/`; overview and the problem list with stages → root `README.md` (keep it current).
- Exploratory files go in `problems/<problem>/scratch/` (git-ignored, persists across sessions), never in a session temp folder. Experiments worth keeping become `solver/src/bin/<name>.rs`; their conclusions go in the log.
- **Computation:** new code reproduces known values before its new values count. A search's scorer is frozen during a run; a change is a new version, logged. Re-verify any new best independently.

## Conventions
- **Problem folders:** kebab-case (`catch-up`). The problem's Lean library is the same words in UpperCamelCase (`CatchUp`); its solver crate keeps the folder name.
- **Lean files:** UpperCamelCase, one file per topic (`CatchUp/Parity.lean`); `Statement.lean` holds only the goal statement, marked pending in its doc comment until the user approves it.
- **Lean names:** [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html): theorems snake_case (`parity_law`), value-computing definitions lowerCamelCase (`valueAux`), types and `Prop` definitions UpperCamelCase (`Conjecture`), all in the problem's namespace (`CatchUp.parity_law`).
- **Rust names:** [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html): modules, functions and files snake_case, types UpperCamelCase. An experiment binary is named after the question it answers (`quad_step`).
- **Blueprint:** [leanblueprint](https://github.com/PatrickMassot/leanblueprint) style in Markdown: an index table (ID, Name, Statement, Uses, Line, Lean, Status, Approved) and one section per lemma with its paper proof and evidence. Line lists the lines it serves (`A1, A2`); the goal node has `all`.
- **IDs:** lines of attack `A1`…, blueprint lemmas `L1`…, backlog ideas `B1`…, obstructions `O1`…; stable through reordering, never reused. Log entries are referenced by their heading (`<date>: <title>`). Cross-references use IDs ("O1 rules out B4").
- **Scratch:** experiment output is named `<experiment>-<args>.<ext>` (`quad_step-30.md`); agents may keep a working folder (`scratch/refuter/`). Nothing in scratch counts as a result.
- **Dates:** ISO 8601 (`2026-10-22`).
- **Commits:** [Conventional Commits](https://www.conventionalcommits.org) `type(scope): summary`, then a body with what and why. Scope: the problem folder, or the repo area (`principles`, `tools`, `templates`, `workflow`). Types: `feat`, `fix`, `explore` (attack work on a problem), `results`, `docs`, `refactor`, `perf`, `test`, `chore`. One logical change per commit, never two problems in one.
- **Log:** every entry has all seven fields of the format in `templates/problem/log.md`, unused ones stated ("not run", "not searched"). Append-only: a mistake gets a new entry naming the one it corrects.
- **Results:** `results/` holds only our own computations (literature values go to the README, debug runs to `scratch/`). One file per run, `results/<quantity>[-<scope>].md`, never edited; a newer run whose scope contains the old one replaces it. Header: Date, Command, Commit, Machine, Runtime, Checked (independent verification, or "unchecked"); where they apply, Inputs (seeds, external data with version or hash), Scope completed (runs cut short), Data (path and SHA-256 of output kept outside git). A search states the exact scope searched and the outcome, including "found nothing". Data a Lean proof reads lives under `lean/`. Other files link to results instead of copying their data; a one-line conclusion is fine.

## Lean
- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`). Ask before bumping.
- Import every module in its library root (e.g. `CatchUp.lean`) once it is `sorry`-free; `lake build` only checks what the roots import. Check an unfinished module with `lake build <Module>`.
- `lake env lean` skips the lakefile's `leanOptions`, e.g. `autoImplicit = false`.
- Start each file with a `/-! ... -/` module doc-string; Mathlib's linter warns otherwise.
- After any Mathlib change, run `lake exe cache get` before building, or Lake compiles Mathlib from source (hours).

## This machine
- The Lean toolchain is on F: because C: is short on space: `ELAN_HOME=F:\WIN_DATA\lean\elan`, `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin` on the user PATH. If `lake` isn't found, the shell predates the install; set them in-process. If VS Code offers to install Lean or elan, it was started without these variables: decline, restart VS Code from the Start menu.
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`, `CARGO_HOME=F:\WIN_DATA\rust\cargo`. Toolchain: MSVC (`x86_64-pc-windows-msvc`) with the installed Visual Studio Build Tools 2022 and Windows SDK.
- GPU: RTX 3060 Ti, 8 GB, driver 610.88 (supports CUDA ≤ 13.3). CUDA Toolkit 13.3 in `C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.3` (`CUDA_PATH`; DLLs in `bin\x64`, which must be on `PATH` for NVRTC).
- RAM: 32 GB, about 16 GB free with the usual apps open. Disks: F: is a SanDisk SSD PLUS 2 TB (QLC, reads ~500 MB/s, writes ~100 MB/s sustained once its cache fills); C: is a Samsung 870 EVO 1 TB. Jobs that spill gigabytes to disk are bound by F:'s writes.
- The user runs every install and download: give them the exact command instead of running it.
