---
name: choose
description: Picks a new problem from problems/problems.md and sets it up: checks the best candidates are still open and not crowded, frames them by kind against this machine, the user picks; then creates its folder, writes the problem, states the goal and draws the first ideas.
disable-model-invocation: true
---

# Choose a problem

1. Take the user's recent picks in `problems/candidates.md` and the
   best-scored `open` problems in `problems/problems.md`, each whose kind
   has a skill and that `problems/active.md` doesn't list.
2. For each: is it solved (recent arXiv, the source's own records), and who
   is on it now (the watch lists in `problems/problems.md`, AI-assisted
   claims in the last 90 days)? Update its Status and Checked date.
3. Frame it in each kind that could apply (CLAUDE.md, Problem). For each
   framing estimate what it needs (compute, memory, the cost of the Lean
   check, whether it hinges on a new idea) against this machine (CLAUDE.md,
   This machine). Keep only framings that fit and whose kind has a skill.
4. The user picks a problem and its framing.
5. Everything here is done in the main folder on main. Add the problem to
   `problems/active.md`, remove it from `candidates.md`. Copy
   `templates/_shared/` and `templates/<kind>/` to `problems/<name>/`;
   rename `lean/Problem*` and the namespace to the library name, and the
   crate to the folder name. Add a `[[lean_lib]]`
   with `srcDir` and a `defaultTargets` entry to `lakefile.toml`.
6. Write the README (`template/README.md`): the question and its status,
   Solutions (none yet), problem and goal, literature with dated searches,
   and under Working on it the kind, modules and estimate.
7. State the goal in Lean and run `audit`; the user approves it.
8. Start the attack as the kind's skill says under Start; set
   `understanding.md` and `state.md`.
9. Commit everything on main; once the tree is clean, create the problem's
   worktree (CLAUDE.md, Rules) for the researcher.
