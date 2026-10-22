# AI and computation

## What AI is good and bad at
- Outputs are random draws: usually near-correct, with subtle errors. Use it interactively, not "click once and forget". `[Views]`
- Capability is jagged: astounding on objectively checkable, well-documented tasks, poor on subjective ones or where data is scarce. `[Math2]`
- Good at: literature search (when checked), code, plots, routine calculations, adapting an existing proof, checking many cases, red-teaming text. `[Methods]` `[Fut]` `[o4]`
- Weak at: knowing when it took a wrong turn; judging whether a subproblem is easier; intuition, definitions, asking the right question; showing its process. `[Lex]` `[Litt]` `[NoHeroes]`
- As a collaborator: over half its ideas are rubbish, known, or irrelevant; around 20% are a useful new observation. Only an expert can filter; a non-expert is more likely led astray. `[Fut]`
- Recurring blind spots seen in practice: flipping equations (x = f vs f = x), off-by-one starts (0 vs 1), notation clashing with Mathlib, wrong lemma statements. `[o4]` `[Copilot]`
- Hit rates reported by working mathematicians: ~80% of generated arguments wrong, ~1 in 10 suggestions useful; still worth it because it runs while you do something else. `[GS]`
- Stronger at constructions and counterexamples, and at combining known techniques from areas few people know together (the unit-distance disproof used 1960s class field theory). Weaker at proving true conjectures that sit inside a large theory and need a new technique. `[LittA16z]` `[GowersSummer]`
- Short outputs are checkable and asking "is that correct?" often gets an honest no; very long outputs (an 800-page AI "proof") are beyond what the model can check, so assume wrong. Harnesses that push for more output lower reliability. `[LittA16z]`
- Mode collapse: different users get the same proof of the same theorem. AI exploration is less diverse than a community's. `[LittA16z]`
- It can't tell you how it found an idea, or how original the idea is; and it explains at the level of someone who already understands. `[GowersMP]`
- What benchmarks measure in models is mostly knowledge: a model that has memorized the literature doesn't need the reasoning a human needs to find the intermediate result. Problem difficulty for humans is a poor guide to difficulty for models. `[LittEpoch]`
- Models know a lot of advanced theory but in some fields mostly try to find the result in the literature plus one or two steps; their ideas for deep open problems are "almost always nonsense". They can't yet learn a new object by playing with it. `[LittEpoch]`
- AI results cluster where the community was already close: the last mile after human work, or problems few people had looked at. `[LittCMSA]` `[NSWeek]`
- Models underestimate their own capability (one estimate: 20–30x on formalization time) and AI-written prompts over-constrain. Keep instructions lean; revisit them when models change. `[Ilin]`

## How to use it
- **Red team over blue team.** Prefer AI for criticizing and stress-testing; use it for generation only where you can check the result yourself. Pose your own strategy and ask it for a critique, rather than asking for a strategy. `[Methods]` `[Views]`
- **Rule of thumb:** if you couldn't present the AI's output and answer questions on it without the AI, it doesn't belong in the workflow. `[Methods]`
- **Bite-size pieces.** An expert splits the task and checks each piece: maybe 3x faster, not push-button. A 100-step chain at 99% per step fails; a cohort of 100 independent problems at 20% solves 20. `[Fut]`
- **Tiered effort.** Cheap automated tools clear the easy cases; frontier AI and humans take the hard residue. `[Workflows]` `[ETP]`
- **Keep productive friction**: offload tedium you can spot-check, keep the hard thinking that builds understanding. Mental diet, like food after the Green Revolution. `[Views]` `[Fut]`
- **Before granting an agent autonomy:** the task is non-critical, self-contained, deterministic and sandboxed, doesn't replace a core skill, doesn't compete with humans. `[Views]`
- **Find the better statement.** Litt couldn't get any model to prove a lemma; working examples by hand suggested a sharper, more conceptual statement, which the models then proved quickly. Today a model proves the original with a 10-page grind and never finds the better statement. When a proof is a grind, look for the statement that explains it. `[LittCMSA]` `[LittA16z]`
- **Reduce, don't one-shot.** Gowers's group builds Pólya-style "moves" (generalize, specialize, add a hypothesis…) to break a problem just beyond the model into pieces it can do, keeping the motivation visible. That is the job of our loop. `[GowersMP]`
- **Gowers's workflow** (May 2026): ask for a result → ask for a write-up as a LaTeX preprint → ask it to extend → ask it to check its own technical statements → an expert in the area verifies. `[Gowers55]`
- **AI review of your own write-ups works**: Litt ran all his papers through one; ~400 comments, ~98% correct, five theorems missing a hypothesis. Run it on every write-up. `[LittCMSA]`
- **The cost of trying something is collapsing.** Many conjectures were stated without anyone running the obvious computation; those now fall. Before stating a conjecture, run the check yourself. `[LittEpoch]`
- **Delegate, don't wait.** Design the high-level structure (main statements, likely lemmas), hand it to the AI, move on to something else, run several in parallel; treat the AI as a team of tireless junior collaborators. Sitting and waiting on each call wastes its value. `[Aristotle]`
- **Sometimes no LLM is the answer.** In Tao's SAIR competitions the winning distillation entries barely used LLM calls, and the winning team in the inverse Galois hunt was two experts using traditional computation. `[SAIR]`
- **Prefer problems whose answers are cheap to check** (a construction you can verify), so evidence arrives before anyone reads a long proof. `[LittCMSA]`

## Computation and search
- **Experimental math is now cheap.** Do "population surveys" (many cases, a whole family of problems) rather than single case studies; map which methods solve which cases. `[Math2]` `[Fut]`
- **Evolve programs, not answers.** Have the model write code that generates candidates; short code tends to find structured answers and can be parameterized by n to generalize. `[AE]`
- **The scorer is the hard part, and it will be exploited.** AlphaEvolve passed float tolerances with near-duplicate points, used degenerate inputs, and exploited an LP solver's failure mode. Use exact or interval arithmetic, check every side condition, score only what is provable, raise errors on solver failure, re-verify winners independently. `[AE]`
- **Feed history.** Give each round the record of past successes and failures. `[AE]`
- More exploits seen: roots placed just off the unit circle to be miscounted, `mpmath` root-finding precision at high degree, double roots that stall Newton's method. Each fix invited the next exploit; assume cheating and check by hand. `[GS]`
- The prompt matters a lot: hints (expected symmetry, where the points cluster) beat pure RL baselines; ask for code that generalizes to all n; encouraging wording measurably helped. Overnight runs cost about $1–5 per problem in model calls. `[GS]`
- **Problem generation from the literature**: "here are 10 problems this method did well on; find 10 similar ones" gave 5 bad, 4 known, 1 new and good. `[GS]`
- **Search methods, cheapest first** `[Wagner]`: naive RL (each move a choice, score at the end) is simple but rarely works on harder problems. A local–global loop does better: build a big, diverse database of good constructions, train a model on them, sample new ones, improve each by greedy local moves, repeat (PatternBoost). Searching over short programs avoids the ugly local optima, since optimal objects tend to have short programs. To keep throughput, evolve search heuristics that run ~100 s each instead of single constructions, or "improvers" that start from the best so far (loses interpretability).
- **Advice steers search.** The same run seeded with advice from someone who thought 30 minutes beat 5 minutes beat 2 minutes beat none, and the output keeps "the melody" of the advice. Compare battle plans by running each as its own search. For generalization, score a program over many values of n and average. `[Wagner]`
- **Don't keep changing the objective.** Hales kept adjusting the Kepler score function whenever he got stuck; each change saved months but made the proof a mess no referee could fully certify. Freeze scorers and version them. `[MAP]`
- **Scientific code you didn't read is low quality by definition.** Check it with unit tests against examples you worked out by hand. `[LittCMSA]`
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
