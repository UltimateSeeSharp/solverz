# solverz

AI-assisted attacks on open math problems; every result is checked in Lean 4.
How we think and work: `principles.md`.

## Domain model
- **Problem**: what we want to solve. Statement (as a Lean claim), kind,
  core difficulty (what any solution must get past), literature. Kinds:
  - `prove`: a statement holds in all cases; a Lean proof.
  - `find`: an object with a property exists; Lean checks the object.
  - `bound`: improve a best-known value; an object from below, a proof
    from above.
  - `compute`: an exact value or complete list; Lean checks a certificate.
  A problem that fits no kind, or has no finite check, is not taken on;
  the user decides.
- **Idea**: a way to attack the problem. Kind (induction, invariant, finite
  reduction, …), source (ideator, literature, us), the claims it needs,
  including the claim that those claims imply the goal.
  Status: `new` → `alive` | `dead` (which claim failed) | `solved`.
- **Claim**: one precise statement. The claims it uses; evidence; what was tried and failed.
  Status: `open` → `refuted` (counterexample) | `proved` → `verified` (Lean).
  `approved` when the user confirmed its Lean statement says what we mean.
- **Experiment**: a computation that tests one claim. States beforehand which
  result changes the claim's status; its code first reproduces known values.
- **Journal**: what changed, newest last: one timestamped line per step that
  changed a status, under its date.

Relations: an idea needs claims, a claim uses claims (both many to many).
A refuted claim kills every idea that needs it; an idea whose claims are
all verified solves the problem.

## Where things live
```
problems/<name>/
  README.md     the problem
  ideas/        ideas.md (index), I1.md, I2.md, …
  claims/       claims.md (index), C1.md, C2.md, …
  experiments/  experiments.md (index), E1.md, E2.md, …
  journal.md    what changed, newest last
  state.md      now: focus, next step, running jobs, what needs the user
  lean/         <Name>.lean (root); <Name>/Statement.lean (the goal and the
                definitions it uses), Defs/ (other definitions), Claims/
                (proofs; each header names its claim IDs), Tests/
  solver/       README.md (engines, how each is checked); src/lib.rs,
                src/engines/, src/bin/ (experiments, named by ID: e12_quad_step.rs)
  scratch/      git-ignored playground
```

## Rules
- Agents and experiments run in the background while work goes on; each is
  listed under Running in `state.md` until its result is recorded.
- One attack at a time on this machine; switch branches only with nothing
  under Running.
- At most 3 agents at a time.
- Experiments may use whatever RAM, CPU and GPU is free, keeping about 4 GB
  RAM and 2 threads spare so the system doesn't swap or lag; one GPU job at a
  time. An experiment that can't fit on this machine is not run.
- Never edit an approved statement; a change is a new claim.
- Experiments add new code in `solver/src/bin/`; they never change code that
  earlier results depend on.
- The attack loop works on the long-lived branch `attack/<problem>`: created
  from main the first time, main merged into it whenever work starts,
  one commit per step. The user merges it into main.

## Workflows

### Choose: a new problem
The `choose` skill.

### Attack
"attack <problem>" starts the workflow of the problem's kind. On every start,
the loop first reads `state.md` and the files it links, checks each job under
Running (reads its output, or reruns it if lost), and continues from its next
step.

#### `prove`
1. Pick the most promising idea now: new ideas get their cheapest kill test
   first, alive ones go deeper. Work only on claims a live idea needs.
2. Work on one claim: test it, prove it, find it in the literature, or
   verify it in Lean (once every claim of its idea is proved on paper;
   reported claims go through `audit` first).
3. Before a claim becomes `proved` or `refuted`, the `refuter` attacks the
   result; the change goes through on SURVIVES. REFUTED: the claim is
   `refuted` once its counterexample is rechecked. FLAWED: it stays `open`,
   the flaw under Tried. UNCLEAR: settling it is the next step.
4. Record statuses, a journal line and `state.md`.
5. The goal claim verified: stop and tell the user. Otherwise never stop:
   out of ideas, the `ideator` draws more. The user can stop the loop at any
   time.

#### `find`

#### `bound`

#### `compute`

## Helpers
- `ideator` (agent): draws ideas with the claims they need.
- `refuter` (agent): attacks claims: counterexamples, proof checks.
- `choose` (skill): finds a problem and sets it up.
- `audit` (skill): prepares a claim's Lean statement for the user's approval.

## Trust
- A result counts only once Lean checks it: `lake build --wfail`, no `sorry`,
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
- **IDs:** ideas `I1`…, claims `C1`…, experiments `E1`…; stable, never reused.
- **Lean:** one file per topic, UpperCamelCase (`CatchUp/Parity.lean`).
  Names follow
  [Mathlib's conventions](https://leanprover-community.github.io/contribute/naming.html):
  theorems snake_case, value-computing definitions lowerCamelCase, types and
  `Prop` definitions UpperCamelCase, all in the problem's namespace.
- **Rust:** [API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html)
  naming; an experiment binary is named after the question it answers.
- **Scratch:** `problems/<name>/scratch/` is git-ignored; nothing there counts.
  Exploring there to find ideas is always allowed; the rules apply to what
  gets recorded.
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
- After any Mathlib change, run `lake exe cache get` before building, or
  Mathlib compiles from source (hours).

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
