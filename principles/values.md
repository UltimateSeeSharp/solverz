# Values

## What counts as done
- Solving is only the first rung: **solve → verify → explain → digested by others → part of the field's standard theory**. AI accelerates the first two; the last is the most valuable. `[ICM]`
- **Digested** means someone can give an expert talk on it and take questions. A proof no human can explain is incomplete, even if Lean checked it. `[ICM]` `[Workflows]`
- AI write-ups put emphasis in the wrong places (pages on a trivial lemma, one line on the key step) and skip citations. Write-ups must say what the key idea is, where the difficulty was, and what came before. `[ICM]` `[Workflows]`
- Problems are "lighthouses": what's learned on the way (successes, failures, partial results) is worth more than the answer. Solving should generate follow-up questions. `[Math2]` `[NoHeroes]`
- Goodhart's law: optimizing one proxy (problems solved) decouples it from the real goals (understanding, techniques, training). State both the explicit and the implicit goals. `[ICM]` `[Workflows]`

## What to record
- **The process, not just the result**: dead ends, partial results, how a claim was weakened to survive. AI can't show its process; open logs (Polymath) can, and students learn most from them. `[NoHeroes]` `[Fut]` `[Lex]`
- **Negative results and failed literature searches**, or the next person repeats them. `[Fut]` `[AE]`
- Resource use (time, compute) alongside results. `[Math2]`

## Toward others
- **Disclose** AI and tool use; humans take responsibility for correctness and authorship; attribute properly, including when an AI rediscovers a known argument. `[Leiden]` `[1026]`
- **Don't play the slot machine for theorems.** Litt had an agent "find five recent conjectures and prove them": three correct, publishable-looking papers in an hour, no understanding gained. A paper no human has engaged with can't be high quality. `[LittCMSA]` `[LittA16z]`
- **Answer first, insight second.** When an AI answer arrives before understanding, don't stop at the answer: read it as little as possible, take a hint, try to prove things yourself, take the next hint. `[GowersSummer]`
- The new bar for a contribution: prove something the models can't prove alone, possibly with their help. `[Gowers55]`
- **Don't strip-mine.** In October 2026 a lab released ~300 AI proofs without consulting anyone, wiping out junior researchers' projects. Before attacking a problem, check whether someone is working on it; prefer problems where the work adds understanding. `[NoHeroes]`
- Second proofs and partial results still have value; don't abandon a line because AI might get there first. `[Taback]`
- Beware sharing unpublished ideas of others with commercial models. `[Golden]` In September 2026 researchers who had used a lab's models on unpublished Navier–Stokes work, or left a draft on an unlinked web page, worried their work had reached a competitor's training data. Turn off training on your data; treat anything online as public. `[NSWeek]`
- **Check exactly which version was solved.** The October Navier–Stokes result is the forced equation; the unforced Millennium version is still open. Read the statement before the headline. `[NSWeek]`
- **Release failures.** AlphaEvolve's paper listed where it failed; labs' logs of failed attempts would teach more than their wins. `[NSWeek]` `[AE]`
