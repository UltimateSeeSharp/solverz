---
name: choose
description: Finds a new problem and sets it up: shortlists, checks it is open and not crowded, frames it by kind against our resources, the user picks; then creates its folder, Lean library and solver crate, writes the problem, states the goal and draws the first ideas.
---

# Choose a problem

1. Find candidates: shortlists in `research/selection/`, a fresh survey
   (`tools/survey/`), or the user's suggestion.
2. For each: is it solved (recent arXiv, the source's own records), and who
   is on it now (the watch lists in `research/selection/record-tables.md`,
   AI-assisted claims in the last 90 days)?
3. Frame it in each kind that could apply (CLAUDE.md, Problem). For each
   framing estimate what it needs (compute, memory, the cost of the Lean
   check, whether it hinges on a new idea) against this machine (CLAUDE.md,
   This machine). Keep only framings that fit and have a written workflow.
4. The user picks a problem and its framing.
5. Copy `templates/problem/` to `problems/<name>/`; rename `lean/Problem*` and
   the namespace to the library name, and the crate to the folder name. Add a
   `[[lean_lib]]` with `srcDir` and a `defaultTargets` entry to `lakefile.toml`.
6. Write the README: problem, kind and the estimate, core difficulty,
   literature with dated searches.
7. State the goal as claim C1 and run `audit`; the user approves it.
8. Draw the first ideas with the `ideator`, standard techniques first;
   fill `ideas/` and `claims/`, set `state.md`, add the problem to the
   root README.
