---
name: explore
description: One iteration of the research loop on a problem in problems/<name>/ — pick one idea, turn it into a falsifiable claim, try to kill it, have a fresh refuter attack survivors, log the result. Use with /loop for unattended runs, e.g. `/loop /explore catch-up`.
---

# Explore: one iteration

Argument: the problem folder name (e.g. `catch-up`). Work on exactly ONE idea, then stop. Principles cited as `[Tag]` are in `principles/` (sources in `principles/sources.md`).

## 0. Load state (from disk, not memory)
Read `problems/<p>/state.md` first (stage, where things stand, open threads, next step, awaiting review), then `README.md` (statement, agent rules), `backlog.md`, `obstructions.md`, the last 5 entries of `log.md`, `solver/README.md` (engines and experiments to reuse) and `principles/README.md`. Don't touch open items under "Awaiting review" in `state.md`, or another thread's work; work on something else.

## 1. Diverge, then pick
Write down 3 candidates: the next step from `state.md` (or the best open backlog item); a variation of the best result so far; one idea unlike anything logged (a different angle: strategy, invariant, stronger general statement, toy variant, a known result from another field) `[Lex]` `[Dumb]`. Skip anything already in the log or ruled out in `obstructions.md`. If the last 3 log entries share one approach and all failed, don't pick it. Pick one; add the other two to the backlog.

## 2. Make a claim
State it precisely and falsifiably, with the prediction it makes. Before testing: how would it be used if true, would a weaker claim do `[Ahead]`?

## 3. Try to kill it, cheapest first
- Smallest cases and extreme cases first; a counterexample ends the iteration early, which is fine `[Sceptical]`.
- Fit on small sizes, test on larger ones with no changes; a rule with nearly as many special cases as data points is overfitting `[Lex]`.
- Experiments: new files only, `solver/src/bin/<name>.rs` (or the problem's equivalent); first reproduce known values with the new code. Keep runs under ~10 minutes. Scratch output in `problems/<p>/scratch/`.
- Scorers and evaluators: exact arithmetic, every side condition checked, re-verify any winner independently `[AE]`. Prefer reusable evaluators so later iterations improve the best candidate instead of starting over.

## 4. Refute (survivors only)
If the claim survived step 3, spawn the `refuter` agent with: the claim, the evidence, the files and commands. It tries to break the claim, audits the experiment, and searches the literature. Record its verdict and reasons as given.

## 5. Record
Append to `log.md` (format at its top): claim, experiment (file + command + runtime), outcome, refuter verdict, meaning. Failures get the counterexample, why it failed, and how the claim could be weakened to survive `[NoHeroes]`. Also record literature searches, including ones that found nothing `[Fut]`.
- A counterexample to a generalization goes into `obstructions.md`: what fails, and which proof approaches it rules out `[Lex]`.
- Update `backlog.md`: remove the item, add follow-ups.
- A new experiment worth keeping goes into the table in `solver/README.md` (question, command).
- A claim that holds everywhere computable and survives the refuter: write a paper proof sketch in the log, run the checklist in `principles/scepticism.md`, and add it to `blueprint.md` as status `conjectured` or `paper proof`.

## 6. Checkpoints: stop and hand over
Never do these unattended; add the item under "Awaiting review" in `state.md` with what the user must decide, then end the iteration:
- a new or changed Lean statement (the user approves every statement);
- calling anything proved, new, or a solution;
- commits, pushes, installs, toolchain changes;
- editing files the problem's README marks as off-limits, or compute beyond the budget.

## 7. Hand over: rewrite `state.md`
The next iteration starts from this file, so leave it complete and current (format: `templates/problem/state.md`). Rewrite, don't append: update "Where things stand", "Open threads", "Awaiting review" and the date, and set "Next step" to one concrete action with its reason. Change the stage only when the workflow's criterion is met (`CLAUDE.md`, Workflow), e.g. Explore → Consolidate once a claim on the main line survives the refuter.

## 8. End
Three lines: idea, result, next. Explain in plain terms; the user is a developer, not a mathematician.
