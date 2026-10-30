---
name: choose
description: Picks a new problem from problems/problems.md and sets it up: checks the best candidates are still open and not crowded, frames them by kind against this machine, the user picks; then creates its folder, writes the problem, states the goal and draws the first ideas.
---

# Choose a problem

1. Take the best-scored `open` problems in `problems/problems.md` whose kind
   has a written workflow and that `problems/active.md` doesn't list.
2. For each: is it solved (recent arXiv, the source's own records), and who
   is on it now (the watch lists in `problems/problems.md`, AI-assisted
   claims in the last 90 days)? Update its Status and Checked date.
3. Frame it in each kind that could apply (CLAUDE.md, Problem). For each
   framing estimate what it needs (compute, memory, the cost of the Lean
   check, whether it hinges on a new idea) against this machine (CLAUDE.md,
   This machine). Keep only framings that fit and have a written workflow.
4. The user picks a problem and its framing.
5. Add the problem to `problems/active.md` and commit that on main; then
   create its worktree (CLAUDE.md, Rules), where everything from here is
   done and committed. Copy `templates/problem/` to `problems/<name>/`;
   rename `lean/Problem*` and the namespace to the library name, and the
   crate to the folder name. Add a `[[lean_lib]]` with `srcDir` and a
   `defaultTargets` entry to `lakefile.toml`.
6. Write the README: problem, kind and the estimate, literature with dated
   searches.
7. State the goal as claim C1 and run `audit`; the user approves it.
8. Draw the first ideas with the `ideator`, standard techniques first;
   fill `ideas/` and `claims/`, set `understanding.md` and `state.md`.
