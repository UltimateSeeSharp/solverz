---
name: solve
description: The loop every problem runs: start, loop, stopping. `/solve <problem>` (its folder name); loads the modules the problem's README lists.
disable-model-invocation: true
---

# Solve

**NEVER STOP** until the user interrupts (Esc). When the problem is solved
(Loop), tell the user. When a step has to wait (on Running, the user, the
machine, …), take one that doesn't (paper work, Lean statements, checking
code before it runs, …).

## Start

1. `/solve <problem>` starts this skill, with the problem's folder name.
2. Enter the problem's worktree (CLAUDE.md, Rules).
3. Check `git status`.
4. Merge main into it.
5. Load the skill of each module the README lists.
6. Read `understanding.md`, `state.md` and the files they link.
7. Check each job under Running: read its output, or rerun it if lost.
8. Continue from its next step.

## Loop

1. **Pick** the most promising idea now, in light of `understanding.md`:
   - new ideas get their cheapest kill test first;
   - alive ones go deeper;
   - with no next idea of its own, the researcher brings in the `ideator`;
     nothing waits on it.
2. **Work** on one claim it needs: test it, prove it, find it in the
   literature, or verify it in Lean.
   - Verify it in Lean while it is open, when Lean settles it faster than
     paper; otherwise once every claim of the idea is proved on paper.
3. **Check** before a claim becomes `proved` or `refuted`: the `refuter`
   attacks it (CLAUDE.md, Roles); a flaw goes under Tried. Its report is
   recorded as a Review (`reviews/R<n>.md`, its scripts in `R<n>/`).
   - A counterexample refutes a claim once it is an Experiment's outcome
     (CLAUDE.md, Files); in Lean if the claim is stated there and the check
     is quick.
4. **Record** changed statuses with a journal line, and `state.md`.
5. **Lean proves the goal (README) or its negation:** that theorem goes under
   "Needs the user" as a proposed Solution (CLAUDE.md, Files); tell the user.

## Stopping

- Never stop for context: compaction is automatic; `state.md` carries the
  loop.
- After answering the user, go on with the loop.
