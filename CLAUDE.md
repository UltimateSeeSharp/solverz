# solverz

AI-assisted attacks on open math problems; every result is checked in Lean 4.

## Problem

What we want to solve, of one kind; each kind adds its own model and attack
loop: the skill of its name.

- `prove`: a statement holds in all cases; a Lean proof.
- `find`: an object with a property exists; Lean checks the object.
- `bound`: improve a best-known value: a better object, or a proof of a
  tighter limit; Lean checks either.
- `compute`: an exact value or complete list; Lean checks a certificate.

A problem that fits no kind, or has no finite check, is not taken on; the
user decides.

## Where things live

```
.claude/               skills and agents
templates/             what a new problem is set up from (Files)
problems/              the problem lists and one folder per problem (Files)
toolbox/               techniques to draw on; toolbox/check.ps1 validates it
principles.md          how we think and work
.worktrees/<problem>/  the git worktree each problem's attack runs in (Rules)
```

## Files

Every problem has these (`templates/_shared/`); its kind adds more (`templates/<kind>/`), described in its skill.
In a template, `<…>` in the text and `{…}` in file and folder names are placeholders to replace.

| File               | What it holds, how it is used                                                                                                                                                                                                                                                                                                                                            |
| ------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `README.md`        | The problem in plain terms, the goal with its Lean name, its kind; the literature, with dated searches, including those that found nothing; optional constraints for working on it (files not to edit, compute limits).                                                                                                                                                  |
| `state.md`         | Now: the focus, the next step, what is running (agents and experiments: what, when started, where its output goes) and what needs the user.                                                                                                                                                                                                                              |
| `understanding.md` | What holds (heuristics marked as such), what blocks every approach so far, and so what a Solution must do; each point cites its evidence by ID. Rewritten when the understanding changes; single failures stay in the files of what they tested.                                                                                                                         |
| `lean/`            | The problem's Lean library: `<Problem>.lean` imports its modules; `<Problem>/Statement.lean` holds the goal and the definitions it uses; `<Problem>/Tests/` unit-tests the statements; `<Problem>/<Author>/`, if any, holds Lean imported from that author, with its license and notice; everything else is ours.                                                        |
| `solver/`          | The problem's Rust crate: `README.md` lists its engines and what each was checked against; `src/` holds the engines; `src/bin/` holds its binaries.                                                                                                                                                                                                                      |
| `experiments/` | Its Experiments (`E1`…): computations whose outcome is used as evidence. What one tests and decides is stated before it runs, on committed code validated first (it reproduces known values or objects and rejects broken ones, or agrees with an independent computation). Any other computation is exploration in `scratch/`. |
| `scratch/`         | Git-ignored playground; nothing there counts. Exploring there is always allowed; the rules apply to what gets recorded.                                                                                                                                                                                                                                                  |
| `journal.md`       | Steps that changed a status, newest first; one timestamped line each, under its date.                                                                                                                                                                                                                                                                                    |
| `solutions.md`     | Its Solutions (`Z1`…), newest first: Lean-checked statements that solve a published open question (a table entry, a record, a conjecture). One is listed once the refuter SURVIVES it, its origin credits whoever had it first, and the user approves it. Until then it waits under "Needs the user" in `state.md`; `solutions.md` gets it only on approval. |

## Roles

| Role       | Who             | Started by                  | Job                                                                                                                                                                                                                                                                                           |
| ---------- | --------------- | --------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Researcher | main session    | "attack <problem>" (Attack) | Runs the attack loop. It knows what the problem's files hold, decides what is most promising and works it itself; it never hands its line off or waits. It keeps `understanding.md` current: rewritten when its understanding changes; single failures stay in the files of what they tested. |
| Ideator    | agent `ideator` | the researcher              | Brings fresh angles; its ideas are proposals. Optional, never a step anything waits on; a round takes 30–90 min.                                                                                                    |
| Refuter    | agent `refuter` | the researcher              | Tries to break something before its status changes (a proof, a computation's outcome, a Lean statement, …). SURVIVES: the new status stands. REFUTED: it is wrong; its opposite is recorded. FLAWED: the old status stays, the flaw is recorded. UNCLEAR: settling it is the next step.                     |

## Attack

**NEVER STOP** until the user interrupts (Esc). When the problem's skill says
it is solved, tell the user. When a step has to wait (on Running, the
user, the machine, …), take one that doesn't (paper work, Lean statements,
checking code before it runs, …).

### Start

1. "attack <problem>" invokes the skill of the problem's kind.
2. Enter the problem's worktree (Rules).
3. Check `git status`.
4. Merge main into it.
5. Read `understanding.md`, `state.md` and the files they link.
6. Check each job under Running: read its output, or rerun it if lost.
7. Continue from its next step.

### Stopping

- Never stop for context: compaction is automatic; `state.md` carries the
  loop.
- After answering the user, go on with the loop.

## Rules

### Agents and experiments

- They run in the background while work goes on; each is listed under
  Running in `state.md` until its result is recorded.
- At most 3 agents at a time, each with `model: opus` (always the newest Opus).
- Experiments may use whatever RAM, CPU and GPU is free, keeping about 4 GB
  RAM and 2 threads spare so the system doesn't swap or lag; one GPU job at a
  time. An experiment that can't fit on this machine is not run.

### Statements

- Never edit an approved statement; a change is a new statement.

### Worktrees

- Each attack runs in its own worktree `.worktrees/<problem>/` on the
  long-lived branch `attack/<problem>`.
- It is made once and reused by every session of that problem.
- One commit per step.
- Only the researcher works in a worktree; everything else (choose,
  maintain, …) works in the main folder, on main.

### Trust

- Nothing counts until Lean checks it: `lake build --wfail`, no `sorry`,
  no custom `axiom`, no `native_decide`; `#print axioms` shows only
  `propext`, `Classical.choice`, `Quot.sound`.
- Solvers and agents are untrusted.
- Read any downloaded Lean file before compiling it.

### Lean

- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`).
- Import every module in its library root once it is `sorry`-free;
  `lake build` only checks what the roots import. Check an unfinished
  module with `lake build <Module>`.
- `lake env lean` skips the lakefile's `leanOptions` (e.g. `autoImplicit = false`).
- After any Mathlib change, the user runs `lake exe cache get` before
  anything builds, or Mathlib compiles from source (hours).

### The user decides

Each of these goes under "Needs the user" in `state.md`; mention it, and keep
working on what doesn't depend on it.

- Approving statements.
- Calling anything a Solution.
- Sharing outside the repo.
- Bumping Lean or Mathlib.
- Merging into main.
- Pushes.
- Installs and downloads.

## Conventions

- **Names:** problem folders kebab-case (`catch-up`); its Lean library the
  same words in UpperCamelCase (`CatchUp`); its solver crate keeps the
  folder name.
- **IDs:** an entity's letter and a number (`C1`, `N1`, `Z1`, …); stable,
  never reused.
- **Lean:** one file per topic, UpperCamelCase (`CatchUp/Parity.lean`).
  Names follow
  [Mathlib's conventions](https://leanprover-community.github.io/contribute/naming.html):
  theorems snake_case, value-computing definitions lowerCamelCase, types and
  `Prop` definitions UpperCamelCase, all in the problem's namespace. Each
  file has a `/-! … -/` module doc-string after its imports.
- **Rust:** [API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html)
  naming.
- **Dates:** ISO 8601 (`2026-10-29`).
- **Commits:** [Conventional Commits](https://www.conventionalcommits.org)
  `type(scope): summary`, a body with what and why. Scope: the problem
  folder or the repo area. One logical change per commit.

## This machine

- CPU: AMD Ryzen 7 3700X (8 cores, 16 threads). GPU: RTX 3060 Ti, 8 GB,
  driver 610.88 (CUDA ≤ 13.3); CUDA Toolkit 13.3 in
  `C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.3` (`CUDA_PATH`;
  `bin\x64` must be on `PATH` for NVRTC).
- RAM: 32 GB. Disks: F: SanDisk SSD PLUS 2 TB (QLC, reads ~500 MB/s,
  writes ~100 MB/s sustained once its cache fills); C: Samsung 870 EVO 1 TB. Jobs that spill gigabytes to disk
  are bound by F:'s writes.
- Lean is on F: (C: is short on space): `ELAN_HOME=F:\WIN_DATA\lean\elan`,
  `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin`
  on the user PATH. If `lake` isn't found, the shell predates the install;
  set them in-process. If VS Code offers to install Lean or elan, decline and
  restart it from the Start menu.
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`,
  `CARGO_HOME=F:\WIN_DATA\rust\cargo`; MSVC toolchain with Visual Studio Build
  Tools 2022 and the Windows SDK.
