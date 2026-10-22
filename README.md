# solverz

AI-assisted attacks on open math problems, with every claimed result machine-checked in Lean 4. Rules and workflow: [CLAUDE.md](CLAUDE.md).

## Workflow

A problem moves through six stages: **Choose → Frame → Explore → Consolidate → Formalize → Digest**. Commands in Claude Code drive it:

| Command | Stages | What it does | Your part |
|---|---|---|---|
| `/choose` | Choose | Surveys open problems, shortlists candidates, sets up the chosen one from `templates/problem/` | pick the problem |
| `/audit-statement <problem> <lemma>` | Frame, Formalize | Writes a Lean statement, reads it back in plain words, unit-tests and attacks it | approve or reject the statement |
| `/loop /explore <problem>` | Explore, Consolidate | The research loop, unattended. Each iteration takes one line of attack and one mode (survey, conjecture, search, prove, literature); claims that survive testing go to the `refuter` agent. It turns from finding claims to proving them on paper as lemmas survive. Every 5th iteration runs `/review`. | answer what it lists under "Awaiting review" |
| `/review <problem>` | Explore, Consolidate | Rescores the lines of attack, replans the next 5 iterations, writes a progress report; also runs by hand | |
| `/formalize <problem> <lemma>` | Formalize | Lean proof step by step, with every deviation from the paper proof listed | read the deviations |
| `/digest <problem> <lemma>` | Digest | Write-up: key idea, where the difficulty was, prior work, follow-up questions | confirm it explains the result |

Each session starts from the problem's `state.md` and rewrites it when it ends, so work continues across sessions. Lemmas climb a promotion ladder in `blueprint.md`, from "observed in data" to "formalized" and "digested". The loop stops on its own and lists what needs you under "Awaiting review" in `state.md`: statements to approve, claimed results, commits, installs, or stalled progress. To continue a problem, open its `state.md`, clear "Awaiting review", then run `/loop /explore <problem>`. Exact stage criteria, the ladder and the stop rules: [CLAUDE.md](CLAUDE.md), Workflow.

## Layout

One folder per problem; one Lean project (one Mathlib) and one Rust workspace at the root point into them.

| Path | Contents | Trusted? |
|---|---|---|
| `problems/<problem>/README.md` | Stable reference: statement, goals, literature, agent rules | No |
| `problems/<problem>/state.md` | Current stage, results, open threads, next step: the handoff between sessions | No |
| `problems/<problem>/lines.md` | Lines of attack: routes to the goal with metric, budget, kill criteria | No |
| `problems/<problem>/log.md`, `backlog.md`, `obstructions.md`, `blueprint.md` | Every attempt (failures included), idea queue per line, ruled-out approaches, lemmas with their promotion status | No |
| `problems/<problem>/lean/` | Lean library `<Problem>` (Mathlib) | Yes, under the trust rules |
| `problems/<problem>/solver/` | Rust crate: search/compute code; kept experiments in `src/bin/`; catalog in its `README.md` | No |
| `problems/<problem>/results/` | Curated solver outputs with run metadata | No |
| `problems/<problem>/scratch/` | Playground, git-ignored | No |
| `principles/` | How we work: problem-solving heuristics, scepticism, AI use, Lean, values; distilled from Tao and others, with sources | No |
| `templates/problem/` | Starting files for a new problem: README, state, lines, log, backlog, obstructions, blueprint, solver/README | No |
| `.claude/` | Skills `choose`, `explore`, `review`, `audit-statement`, `formalize`, `digest`; `refuter` agent | No |
| `tools/survey/` | Problem-finding pipeline (Python, stdlib only) | No |
| `tools/principles/` | Transcript fetcher for principles research (needs `pip install youtube-transcript-api`) | No |
| `research/selection/` | Problem surveys and shortlists | No |

## Setup

1. Install [elan](https://github.com/leanprover/elan), the VS Code "Lean 4" extension and [Rust](https://rustup.rs).
2. `lake exe cache get` downloads prebuilt Mathlib instead of compiling it from source (hours).
3. `lake build` and `cargo build --release`

## Verify

`lake build --wfail` (fails on any `sorry`) and `cargo test --release`; what counts as verified is in the trust rules.

## Problems

| Problem | Stage | State |
|---|---|---|
| [Catch-Up conjecture](problems/catch-up/README.md): optimal play on {1..N} is a draw when 1 + … + N is even | Explore | [state.md](problems/catch-up/state.md) |
| [Collatz](problems/collatz/README.md) | Shelved | — |

- **Choosing a target**: surveys of [Erdős problems](research/selection/erdos.md) and [other formal-conjectures collections](research/selection/collections.md).
