# Lean

## Statements
- **A human writes or reviews every statement that is reported**; proofs can be delegated, helper lemmas included, since Lean checks them. A proof of the wrong statement is worthless. `[Methods]`
- Common misformalizations: a missing degenerate case, swapped "for all" / "there exists". They show up as a statement that is false, suspiciously easy, or fails to imply what it should downstream. `[Methods]`
- **Unit-test statements and definitions**: removing a hypothesis should let a standard counterexample through; basic facts (monotonicity, symmetry, degenerate cases) should hold. `[Methods]`
- Don't hard-code constants; parameterize, so changing one (Tao: 12 → 11) breaks only a few lines. `[Lex]`
- **Lean checks proofs, not definitions.** Forget one axiom of a definition and everything still compiles; it just means something else. Test definitions: prove that standard examples satisfy them (permutations form a group) and that expected theorems follow (Lagrange); Buzzard's team spends an hour per meeting proving basic facts about new definitions, then throws the proofs away. `[Riehl]` `[Buzzard]`
- **Misformalization is the norm, not the exception.** About half of the statements Buzzard's experts wrote were wrong the first time (division by zero, natural-number subtraction); about 20% of formal-conjectures statements were wrong; Aristotle disproved about 30 of one batch. Before trusting a statement, ask a prover to disprove it. `[Buzzard]`
- **"Too easy" catches bad statements.** An AI proof of an explicit number-theory bound used only Bertrand's postulate, which can't be enough; the definition turned out too weak. Also check that a new statement implies the older, weaker known results. `[Aristotle]`
- **Junk values.** Lean gives undefined things a default (x / 0 = 0, a "least element" of an empty set). A misformalized statement can become trivially true through them. Check every statement for division, subtraction on ℕ, minimums and inverses that might be undefined. `[NSLost]`
- **Statements written before the proof miss hypotheses.** Formalizing the proof revealed missing measurability, probability-measure and finite-range assumptions; other assumed hypotheses turned out unnecessary. Expect to revise statements, and each revision goes back to the user. `[ByHand]`
- AI-written definitions are the weakest part: too specialized, badly named (a lemma named after a hypothesis `h1`). Review definitions harder than proofs. For audits, extract a minimal file containing only what the statement depends on. Refactors must not change approved statements. `[Ilin]`

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

- AI helps least with project-local lemmas it never saw in training; give it the local API (names and statements) explicitly. ℕ subtraction and ℕ → ℝ casts cause much of the friction. `[ByHand]`
- Reuse Mathlib and existing libraries instead of re-proving; prompt for reuse. `[Ilin]`

## Lean checks the statement, not your paper proof `[NSLost]`
- An agent looping "edit until it compiles" drifts from the informal proof. It silently repairs wrong steps: given a true claim with a wrong factorization, ChatGPT formalized it with the correct factorization and said nothing. It also swaps correct arguments for simpler ones. Both count as success.
- So a green build proves the Lean statement only. The paper proof in our log may still be wrong.
- Rule: the formalizing agent lists every place the Lean proof deviates from the paper proof, and the paper proof is corrected to match. Never call the informal proof checked because Lean passed.

## Trust `[LeanRel]`
- Believe a proof only after the kernel checked it. Lean had soundness bugs in summer 2026, one allowing a false "disproof" of Collatz.
- Check axioms (`#print axioms`), audit definitions as well as theorem statements, and for important results cross-check with an independent kernel (e.g. lean4lean; see the Lean Kernel Arena).
- Large AI-generated formalizations can be correct yet unmaintainable; a type-checked proof is not a library-quality one. `[Workflows]` `[Math20]`
- **Blueprint**: split a proof into a graph of small lemmas, each formalizable independently. `[Lex]` `[Workflows]` Writing it improves understanding (Scholze), and formalizing shows exactly what each step needs, which can simplify the proof: the liquid tensor project replaced a heavy theory with a weaker one that sufficed. `[MAP]` `[Buzzard]`
- **Formalize before you read.** When someone sends an AI-written proof, ask for a Lean version first; then reading the PDF is worth the time. `[Buzzard]` `[Aristotle]`
- General definitions are worth the wait: an AI defines exactly what one paper needs, so several incompatible "manifolds" appear. Prefer Mathlib's definitions; flag any new one. `[Buzzard]`
