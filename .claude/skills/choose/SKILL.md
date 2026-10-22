---
name: choose
description: Pick the next problem (Choose stage) — refresh the survey, check freshness and who else is working on the candidates, write a shortlist for the user, and set up the problem the user picks from the template. E.g. `/choose`.
---

# Choose a problem

Criteria: `CLAUDE.md`, Workflow, stage 1, and the trust rule on already-solved problems. Pipeline and commands: `tools/survey/README.md`. Principles: `principles/values.md`, `principles/ai-and-computation.md`.

1. **Survey.** Clone the sources into a scratch folder and run the pipeline (extract, classifier agents, rank, freshness). Compare with the last shortlist in `research/selection/` and skip candidates already ruled out there.
2. **Review the top by hand**: statement and known results (`show.py`), forum threads, open formal-conjectures PRs, recent arXiv. Prefer problems whose answers are cheap to check `[LittCMSA]`; skip problems someone is actively working on unless we can coordinate `[NoHeroes]`.
3. **Shortlist** in `research/selection/<date>-<source>.md`: for each candidate the statement in plain terms, why it fits the criteria, who else works on it, and the first line of attack. Present it to the user; never pick for them.
4. **Set up** the problem the user picks: copy `templates/problem/` to `problems/<name>/`, add its Lean library (`CLAUDE.md`, Working on a problem), fill README's Problem, Goals and Known, set `state.md` to stage Frame, and add it to the root README's problem table. The Lean statement comes next, through `audit-statement`.
