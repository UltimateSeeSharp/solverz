# Lean

## Statements
- **A human writes or reviews every statement**; proofs can be delegated. A proof of the wrong statement is worthless. `[Methods]`
- Common misformalizations: a missing degenerate case, swapped "for all" / "there exists". They show up as a statement that is false, suspiciously easy, or fails to imply what it should downstream. `[Methods]`
- **Unit-test statements and definitions**: removing a hypothesis should let a standard counterexample through; basic facts (monotonicity, symmetry, degenerate cases) should hold. `[Methods]`
- Don't hard-code constants; parameterize, so changing one (Tao: 12 → 11) breaks only a few lines. `[Lex]`

## Step-by-step recipe with an agent `[CC]`
One-shot "formalize all of it" ran 45 minutes, ran out of tokens, produced nothing. This worked in about 25:
0. Definitions and notation.
1. Skeleton: every lemma statement, proofs `sorry`. Tell it explicitly not to prove yet; otherwise it overthinks and backtracks.
2. One Lean line per informal line, each justified by `sorry`.
3. Fill the `sorry`s one at a time; extract any repeated sub-step as its own lemma.
- Keep the instructions in a markdown file. Keep the formal proof aligned with the informal one, or the agent "tosses what you gave it and does its own thing".
- Work in parallel: do the steps you want to understand yourself, delegate the ones you're sure of. Small steps also resume cleanly after a crash.
- Models adapt an existing formalization far better than they create one: give worked examples. `[o4]`
- Line-by-line formalization loses the big picture; it suits tedious, non-conceptual proofs. `[Copilot]`
- Check AI-suggested statements; a wrong intermediate claim surfaces only at the end. `[Copilot]`

## Trust `[LeanRel]`
- Believe a proof only after the kernel checked it. Lean had soundness bugs in summer 2026, one allowing a false "disproof" of Collatz.
- Check axioms (`#print axioms`), audit definitions as well as theorem statements, and for important results cross-check with an independent kernel (e.g. lean4lean; see the Lean Kernel Arena).
- Large AI-generated formalizations can be correct yet unmaintainable; a type-checked proof is not a library-quality one. `[Workflows]` `[Math20]`
- **Blueprint**: split a proof into a graph of small lemmas, each formalizable independently. `[Lex]` `[Workflows]`
