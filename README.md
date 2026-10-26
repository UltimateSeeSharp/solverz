# solverz

AI-assisted attacks on open math problems, with every claimed result machine-checked in Lean 4. Rules and workflow: [CLAUDE.md](CLAUDE.md).

## Workflow

A problem moves through three stages: **Choose → Frame → Attack**, done when the goal is formalized. You drive it in plain words:

| You say | Stage | What happens | Your part |
|---|---|---|---|
| "choose a new problem" | Choose | Survey (`tools/survey/`), freshness checks, a shortlist in `research/selection/`; then the chosen problem is set up from `templates/problem/` | run the clones; pick the problem |
| "attack &lt;problem&gt;" | Frame, Attack | Works from `state.md`: computes, conjectures, proves on paper, formalizes in Lean; the `refuter` agent attacks every claim; every 5 log entries it reviews the lines of attack. Statements to report go through the `audit-statement` skill. | answer "Awaiting review" in `state.md` |
| "write up &lt;node&gt;" | any | Before a result is shared outside the repo: key idea, where the difficulty was, prior work, AI and tool use | confirm it explains the result |

Each session starts from the problem's `state.md` and updates it before ending, so work continues across sessions. Lemmas in `blueprint.md` move from `conjecture` to `paper proof` to `formalized`; you approve only the statements we report. A session stops on its own and lists what needs you under "Awaiting review": statements to approve, claimed results, commits, installs, or stalled progress. Stage criteria, statuses and stop rules: [CLAUDE.md](CLAUDE.md), Workflow.

## Layout

One folder per problem; one Lean project (one Mathlib) and one Rust workspace at the root point into them.

| Path | Contents | Trusted? |
|---|---|---|
| `problems/<problem>/README.md` | Stable reference: statement, goals, literature, agent rules | No |
| `problems/<problem>/state.md` | Current stage, results, open threads, next step: the handoff between sessions | No |
| `problems/<problem>/lines.md` | Lines of attack: routes to the goal with metric and kill criteria | No |
| `problems/<problem>/log.md`, `backlog.md`, `obstructions.md`, `blueprint.md` | Every attempt (failures included), idea queue per line, ruled-out approaches, lemmas with status and approval | No |
| `problems/<problem>/writeups/` | Write-ups of results shared outside the repo | No |
| `problems/<problem>/overnight/` | One report per overnight session: summary, units linking the log | No |
| `problems/<problem>/lean/` | Lean library `<Problem>` (Mathlib) | Yes, under the trust rules |
| `problems/<problem>/solver/` | Rust crate: search/compute code; kept experiments in `src/bin/`; catalog in its `README.md` | No |
| `problems/<problem>/results/` | Curated solver outputs with run metadata | No |
| `problems/<problem>/scratch/` | Playground, git-ignored | No |
| `principles/` | How we work: problem-solving heuristics, scepticism, AI use, Lean, values; distilled from Tao and others, with sources | No |
| `templates/problem/` | Starting files for a new problem: README, state, lines, log, backlog, obstructions, blueprint, solver/README | No |
| `.claude/` | Skill `audit-statement`; agents `refuter` and `ideator` (effort max) | No |
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
| [Catch-Up conjecture](problems/catch-up/README.md): optimal play on {1..N} is a draw when 1 + … + N is even | Attack | [state.md](problems/catch-up/state.md) |
| [Collatz](problems/collatz/README.md) | Shelved | — |

- **Choosing a target**: surveys of [Erdős problems](research/selection/erdos.md) and [other formal-conjectures collections](research/selection/collections.md).
