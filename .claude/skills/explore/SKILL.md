---
name: explore
description: One iteration of the research loop on a problem in problems/<name>/. Picks a line of attack and a mode (survey, conjecture, search, prove, literature), does one unit of work, updates the line's metric, logs it, and hands over in state.md. Every 5th iteration runs the review skill instead. Use with /loop for unattended runs, e.g. `/loop /explore catch-up`.
---

# Explore: one iteration

Argument: the problem folder (e.g. `catch-up`). One line, one mode, one unit of work, then stop. Tags like `[AE]` point to `principles/sources.md`; the why behind each rule is in `principles/`.

## 0. Load and gate
1. Read `problems/<p>/state.md`. Stop at once, reporting why, if **Loop** says stopped.
2. If "Iterations since last review" is 5 or more, run the `review` skill instead of an iteration and end.
3. Read `README.md` (statement, agent rules), `lines.md`, the line's part of `backlog.md`, `obstructions.md`, the last 5 entries of `log.md`, `solver/README.md`.

## 1. Choose line, idea and mode
- Default: the **Next step** in `state.md`. Otherwise the line with budget left (`main` first), and its best backlog item.
- Once per review cycle, take the wild slot instead: an idea unlike anything logged (another angle, a toy variant, a stronger general statement, a technique from another field) `[Lex]` `[Dumb]`.
- Skip anything logged, ruled out in `obstructions.md`, or claimed by another session in `state.md` (unless the claim is stale). Claim your thread in `state.md` before working.
- Mode follows from what the line needs next: data it lacks → survey; data without a pattern → conjecture; a candidate to optimize → search; a `survived` blueprint node → prove; a question others may have answered → literature.

## 2. Do the work

**survey**: compute data a line needs. Reproduce known values with the new code first; keep runs under the README's compute limit; store tables in `scratch/`, curated ones in `results/` with run metadata. Prefer populations (all small cases) over single cases `[Math2]`.

**conjecture**: state a precise, falsifiable claim from data and say how it would be used `[Ahead]`. Fit on small sizes, test on larger ones unchanged; nearly as many special cases as data points means overfitting `[Lex]`. Hunt the smallest and extreme counterexamples first `[Sceptical]`. When a proof is a grind, look for the sharper statement that explains it `[LittCMSA]`.

**search**: optimize a candidate (a strategy, a construction, a rule) against a scorer in `solver/src/bin/`. The scorer is frozen while a search runs; changing it is a new version, logged `[MAP]`. Exact arithmetic, every side condition checked, solver failures raise errors `[AE]`. Feed the line's history of best and failed candidates; accept a candidate only if it scores at least the best; re-verify any new best independently and update the line's leaderboard.

**prove**: attack one blueprint node at `survived` on paper, in its section in `blueprint.md`. Use the moves in `principles/problem-solving.md`: switch off all difficulties but one, motivated moves, forward reconnaissance, split by regime. List every case and check each; test each intermediate claim numerically; ask whether the argument proves too much `[Sceptical]`. Partial progress counts: record exactly which part is done and what remains `[Partial]`.

**literature**: one concrete question. Search Google Scholar, arXiv, OEIS, MathOverflow and the web; open what you cite `[1026]`. Record hits and misses in the log and update the README's "Known".

## 3. Refute
Survivors go to the `refuter` agent with the claim or proof, the evidence, and the files and commands: mode `claim` after conjecture or search, `proof` after prove. Record its verdict as given. Promote on the ladder only as far as the evidence allows (`CLAUDE.md`, Workflow).

## 4. Record
- `log.md`: one entry (format at its top), with the line's metric before → after.
- `lines.md`: metric, evidence, spent. A counterexample to a line's claim goes into `obstructions.md` (what fails, which approaches it rules out) and may meet the line's kill criteria; leave the kill to `review`.
- `backlog.md`: remove the item, add at most two follow-ups to the line.
- `blueprint.md`: new nodes and status changes. `solver/README.md`: any experiment worth keeping.

## 5. Stop and hand over
Add to "Awaiting review" in `state.md`, and do not do it yourself:
- anything on the "Never unattended" list (`CLAUDE.md`, Workflow); a new or changed Lean statement goes through `audit-statement` first;
- work beyond the README's agent rules or compute limit.

If a stop rule (`CLAUDE.md`, Workflow) is met, set **Loop** to stopped with the reason.

Rewrite `state.md` (format: `templates/problem/state.md`): release your claim, increase "Iterations since last review", update "Where things stand", and set **Next step** to one concrete action (line, mode, step, reason).

## 6. End
Three lines: idea, result, next. Plain terms; the user is a developer, not a mathematician.
