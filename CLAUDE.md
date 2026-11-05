# solverz

AI-assisted attacks on open math problems; every result is checked in Lean 4.
How we think and work: `principles.md`; techniques to draw on: `toolbox/`
(`toolbox/check.ps1` validates it).

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

## Files

Every problem has these (`templates/_shared/`); its kind adds more (`templates/<kind>/`), described in its skill.
In a template, `<…>` in the text and `{…}` in file and folder names are placeholders to replace.

| File               | What it holds, how it is used                                                                                                                                                                                                                                                                                                                                        |
| ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `README.md`        | The problem in plain terms, the goal with its Lean name, its kind; the literature, with dated searches, including those that found nothing; optional constraints for working on it (files not to edit, compute limits).                                                                                                                                              |
| `state.md`         | Now: the focus, the next step, what is running (agents and experiments: what, when started, where its output goes) and what needs the user.                                                                                                                                                                                                                          |
| `understanding.md` | What holds (heuristics marked as such), what blocks every approach so far, and so what a solution must do; each point cites its evidence by ID. Rewritten when the understanding changes; single failures stay in the files of what they tested.                                                                                                                     |
| `lean/`            | The problem's Lean library: `<Problem>.lean` imports its modules; `<Problem>/Statement.lean` holds the goal and the definitions it uses; `<Problem>/Tests/` unit-tests the statements; `<Problem>/<Author>/`, if any, holds Lean imported from that author, with its license and notice; everything else is ours.                                                    |
| `solver/`          | The problem's Rust crate: `README.md` lists its engines and what each was checked against; `src/` holds the engines; `src/bin/` holds its binaries.                                                                                                                                                                                                                  |
| `scratch/`         | Git-ignored playground; nothing there counts. Exploring there is always allowed; the rules apply to what gets recorded.                                                                                                                                                                                                                                              |
| `journal.md`       | Steps that changed a status, newest first; one timestamped line each, under its date.                                                                                                                                                                                                                                                                                |
| `results.md`       | Its Results (`T1`…), newest first: Lean-checked statements that answer or improve a published open question (a table entry, a record, a conjecture). One is listed once the refuter SURVIVES it, its origin credits whoever had it first, and the user approves it. Until then it waits under "Needs the user" in `state.md`; `results.md` gets it only on approval. |

## Roles

- **Researcher**: the session that runs the attack loop. It knows what the
  problem's files hold, decides what is most promising and works it
  itself; it never hands its line off or waits. It keeps `understanding.md`
  current: rewritten when its understanding changes; single failures stay
  in the files of what they tested.
- **Ideator** (agent `ideator`): brings fresh angles, formed from the
  problem's files alone and not from the researcher's view; its ideas are
  proposals. Optional, never a step anything waits on; a round takes
  30–90 min.
- **Refuter** (agent `refuter`): tries to break a result before it counts.
  SURVIVES: the change goes through. REFUTED: the result is wrong; its
  opposite is recorded. FLAWED: the status stays, the flaw recorded.
  UNCLEAR: settling it is the next step.

## Where things live

```
.claude/       skills/  agents/  hooks/
templates/     _shared/  <kind>/
problems/      problems.md  active.md  candidates.md
  <problem>/   templates/_shared/ + templates/<kind>/
toolbox/
principles.md
.worktrees/<problem>/
```

## Rules

- Agents and experiments run in the background while work goes on; each is
  listed under Running in `state.md` until its result is recorded.
- At most 3 agents at a time, each with `model: opus` (always the newest Opus).
- Experiments may use whatever RAM, CPU and GPU is free, keeping about 4 GB
  RAM and 2 threads spare so the system doesn't swap or lag; one GPU job at a
  time. An experiment that can't fit on this machine is not run.
- Never edit an approved statement; a change is a new statement.
- Each attack runs in its own worktree `.worktrees/<problem>/` on the
  long-lived branch `attack/<problem>`, made once and reused by every
  session of that problem: created from main the first time
  (`git worktree add .worktrees/<problem> -b attack/<problem> main`, then
  `.lake/packages` as a junction to the main folder's), main merged into it
  whenever the loop starts, one commit per step. The user merges it into
  main. The main folder stays on main for all other work.

## Workflows

### Choose: a new problem

The `choose` skill.

### Maintain: the repo itself

The `maintain` skill (`/maintain`); never inside an attack.

### Attack

"attack <problem>" invokes the skill of the problem's kind (the Skill tool,
so its Stop hook loads). On every start, the loop first enters the
problem's worktree (Rules), reads `understanding.md`, `state.md` and the
files it links, checks `git status` and each job under Running (reads its
output, or reruns it if lost), and continues from its next step.

The loop stops only when its skill says the problem is settled. Otherwise
**NEVER STOP**: not to wait for anything under Running, the user or the
machine (take a step that needs none of them: paper work, Lean statements,
checking code before it runs), not for context (compaction is automatic;
`state.md` carries the loop), and after answering the user, go on with the
loop. The user stops the loop by interrupting it (Esc); the skill's Stop
hook (`.claude/hooks/never-stop.sh`) sends every other finished reply back
into the loop.

## Trust

- Nothing counts until Lean checks it: `lake build --wfail`, no `sorry`,
  no custom `axiom`, no `native_decide`; `#print axioms` shows only
  `propext`, `Classical.choice`, `Quot.sound`.
- Solvers and agents are untrusted; their output counts once Lean checks it.
- Read any downloaded Lean file before compiling it.

## The user decides

Approving statements, calling anything a solution, sharing outside the repo,
bumping Lean or Mathlib, merging into main, pushes, installs and downloads.
List it under "Needs the user" in `state.md`, mention it, and keep working on
what doesn't depend on it.

## Conventions

- **Names:** problem folders kebab-case (`catch-up`); its Lean library the
  same words in UpperCamelCase (`CatchUp`); its solver crate keeps the
  folder name.
- **IDs:** an entity's letter and a number (`I1`, `C1`, `E1`); stable,
  never reused.
- **Lean:** one file per topic, UpperCamelCase (`CatchUp/Parity.lean`).
  Names follow
  [Mathlib's conventions](https://leanprover-community.github.io/contribute/naming.html):
  theorems snake_case, value-computing definitions lowerCamelCase, types and
  `Prop` definitions UpperCamelCase, all in the problem's namespace.
- **Rust:** [API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html)
  naming.
- **Dates:** ISO 8601 (`2026-10-29`).
- **Commits:** [Conventional Commits](https://www.conventionalcommits.org)
  `type(scope): summary`, a body with what and why. Scope: the problem
  folder or the repo area. One logical change per commit.

## Lean

- Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lakefile.toml`).
- Import every module in its library root once it is `sorry`-free;
  `lake build` only checks what the roots import. Check an unfinished
  module with `lake build <Module>`.
- `lake env lean` skips the lakefile's `leanOptions` (e.g. `autoImplicit = false`).
- Start each file with a `/-! … -/` module doc-string.
- After any Mathlib change, the user runs `lake exe cache get` before
  anything builds, or Mathlib compiles from source (hours).

## This machine

- CPU: AMD Ryzen 7 3700X (8 cores, 16 threads). GPU: RTX 3060 Ti, 8 GB,
  driver 610.88 (CUDA ≤ 13.3); CUDA Toolkit 13.3 in `C:\Program Files\NVIDIA
GPU Computing Toolkit\CUDA\v13.3` (`CUDA_PATH`; `bin\x64` must be on `PATH`
  for NVRTC).
- RAM: 32 GB. Disks: F: SanDisk
  SSD PLUS 2 TB (QLC, reads ~500 MB/s, writes ~100 MB/s sustained once its
  cache fills); C: Samsung 870 EVO 1 TB. Jobs that spill gigabytes to disk
  are bound by F:'s writes.
- Lean is on F: (C: is short on space): `ELAN_HOME=F:\WIN_DATA\lean\elan`,
  `MATHLIB_CACHE_DIR=F:\WIN_DATA\lean\mathlib-cache`, `F:\WIN_DATA\lean\elan\bin`
  on the user PATH. If `lake` isn't found, the shell predates the install;
  set them in-process. If VS Code offers to install Lean or elan, decline and
  restart it from the Start menu.
- Rust is on F: too: `RUSTUP_HOME=F:\WIN_DATA\rust\rustup`,
  `CARGO_HOME=F:\WIN_DATA\rust\cargo`; MSVC toolchain with Visual Studio Build
  Tools 2022 and the Windows SDK.
