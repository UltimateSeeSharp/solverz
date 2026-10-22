---
name: review
description: Strategy review for a problem in problems/<name>/ — score the lines of attack, kill or shelve lines, reallocate the next cycle's budget, prune the backlog, check literature freshness, apply the stop rules, and write a plain-language progress report. Runs automatically every 5th explore iteration; can be run by hand, e.g. `/review catch-up`.
---

# Review

Argument: the problem folder. No new experiments or proofs here; this step steers.

1. **Read** `state.md`, `lines.md`, `backlog.md`, `obstructions.md`, `blueprint.md`, and every `log.md` entry since the last review.
2. **Score each line**: did its metric move this cycle; what did it cost; did anything meet its kill criteria? Kill (`dead`, citing the obstruction) or shelve (`shelved`, with the reason and what would revive it) where the criteria are met. Never delete a line; its record is the point `[Waste]` `[NoHeroes]`.
3. **Choose the main line**: the line with the best evidence that it could reach the goal, not the one with most work sunk into it. Write one sentence on why.
4. **Allocate** the next 5 iterations: most to the main line, at least one to another active line or the wild slot. A line with no active alternatives gets a new candidate line drafted from the backlog, obstructions or literature (status `active`, with reduction, metric and kill criteria).
5. **Prune the backlog**: at most 10 items per line; merge duplicates; drop items made pointless by obstructions or results.
6. **Literature freshness**: if the README's "Known" was last checked more than 14 days ago, make a literature iteration the first item of the next cycle. Also check that nobody has announced a solution (`CLAUDE.md`, trust rules).
7. **Stop rules**: if no line's metric moved this cycle, increase "Reviews in a row without metric movement", else reset it to 0. At 2, set **Loop** to stopped ("no progress for 2 reviews") and ask the user for direction in "Awaiting review", with the options you see.
8. **Report** in `state.md` under "Last review", for the user, in plain terms, at most 8 lines: what moved, what was ruled out, the main line and why, the plan for the next cycle, anything the user must decide.
9. Reset "Iterations since last review" to 0 and set **Next step** to the first iteration of the plan.
