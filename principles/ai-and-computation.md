# AI and computation

## What AI is good and bad at
- Outputs are random draws: usually near-correct, with subtle errors. Use it interactively, not "click once and forget". `[Views]`
- Capability is jagged: astounding on objectively checkable, well-documented tasks, poor on subjective ones or where data is scarce. `[Math2]`
- Good at: literature search (when checked), code, plots, routine calculations, adapting an existing proof, checking many cases, red-teaming text. `[Methods]` `[Fut]` `[o4]`
- Weak at: knowing when it took a wrong turn; judging whether a subproblem is easier; intuition, definitions, asking the right question; showing its process. `[Lex]` `[Litt]` `[NoHeroes]`
- As a collaborator: over half its ideas are rubbish, known, or irrelevant; around 20% are a useful new observation. Only an expert can filter; a non-expert is more likely led astray. `[Fut]`
- Recurring blind spots seen in practice: flipping equations (x = f vs f = x), off-by-one starts (0 vs 1), notation clashing with Mathlib, wrong lemma statements. `[o4]` `[Copilot]`

## How to use it
- **Red team over blue team.** Prefer AI for criticizing and stress-testing; use it for generation only where you can check the result yourself. Pose your own strategy and ask it for a critique, rather than asking for a strategy. `[Methods]` `[Views]`
- **Rule of thumb:** if you couldn't present the AI's output and answer questions on it without the AI, it doesn't belong in the workflow. `[Methods]`
- **Bite-size pieces.** An expert splits the task and checks each piece: maybe 3x faster, not push-button. A 100-step chain at 99% per step fails; a cohort of 100 independent problems at 20% solves 20. `[Fut]`
- **Tiered effort.** Cheap automated tools clear the easy cases; frontier AI and humans take the hard residue. `[Workflows]` `[ETP]`
- **Keep productive friction**: offload tedium you can spot-check, keep the hard thinking that builds understanding. Mental diet, like food after the Green Revolution. `[Views]` `[Fut]`
- **Before granting an agent autonomy:** the task is non-critical, self-contained, deterministic and sandboxed, doesn't replace a core skill, doesn't compete with humans. `[Views]`

## Computation and search
- **Experimental math is now cheap.** Do "population surveys" (many cases, a whole family of problems) rather than single case studies; map which methods solve which cases. `[Math2]` `[Fut]`
- **Evolve programs, not answers.** Have the model write code that generates candidates; short code tends to find structured answers and can be parameterized by n to generalize. `[AE]`
- **The scorer is the hard part, and it will be exploited.** AlphaEvolve passed float tolerances with near-duplicate points, used degenerate inputs, and exploited an LP solver's failure mode. Use exact or interval arithmetic, check every side condition, score only what is provable, raise errors on solver failure, re-verify winners independently. `[AE]`
- **Feed history.** Give each round the record of past successes and failures. `[AE]`
- **Obfuscate famous problems**: models recall the known answer instead of searching. `[AE]`
- **Numbers to formulas**: compute exact small values, rationalize floats (continued fractions), spot the pattern, then prove it. This plus reinterpretation and a literature search cracked Erdős #1026 in 48 hours. `[1026]`
- **Run the search before stating a conjecture**, and record that it found nothing. `[AE]`

## Running an agent loop `[Cerebras]` `[Karpathy]`
- Drift is the main failure mode: with loose scope, agents wander off within hours. Scope each run tightly and check in often.
- One experiment per run; state on disk (log + git), not in the agent's memory; a crash just means the next run starts fresh.
- Accept a change only if the metric is equal or better; revert otherwise.
- Check that the metric tracks the real goal; agents improve proxies without real gains.
- Fewer, better-targeted proposals beat broad exploration when trials are expensive.
- Log everything.
