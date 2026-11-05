# Lean tactics and automation
Tactics and in-Lean search that produce ordinary proof terms for the kernel, and the audit of what a proof depends on.

### T127 Axiom audit
`prove` `find` `bound` `compute` · stage: lean-tooling
aka: #print axioms, trust base, native_decide, decide +native, bv_decide, nativeEqTrue, sorryAx, skSorryAx, native evaluation, kernel-only
- What: lists the axioms a theorem depends on; `native_decide`, `bv_decide`, Mathlib's `inclusion`, lrat-catcher's default mode and pb-catcher run compiled code and add one auxiliary axiom per use (`…._native.native_decide.ax_…`); Duper declares `skSorryAx`; some lean-smt lemmas are `sorry` with the warning silenced, so `--wfail` misses them.
- Fits when: before any result counts, and after any external tool or new tactic.
- Lean: `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.
- Example: lrat-catcher's default mode: each imported theorem "carries one `native_decide` axiom, visible under `#print axioms`" ([lrat-catcher](https://github.com/leansolving/lrat-catcher)); lean-smt's silenced `sorry` lemmas ([lean-smt](https://github.com/ufmg-smite/lean-smt)).
- See also: T5, T13, T25, T131

### T128 Certificate search inside Lean
`prove` `bound` · stage: lean-tooling · signals: inequality, polynomial
aka: linarith, nlinarith, positivity, linear_combination, Farkas certificate, simplex oracle, Fourier–Motzkin, numeric inequalities, polyrith (dead)
- What: `linarith` finds a Farkas-style linear certificate with an untrusted oracle (simplex by default); `nlinarith` also adds squares of subterms and pairwise products of hypotheses; `linear_combination` checks given cofactors with `ring1`.
- Fits when: closing numeric inequalities once the key terms are supplied; final steps of SOS and LP certificates.
- Lean: kernel terms; `linarith` checks its certificate with `ring`.
- Example: an untrusted oracle finds the coefficients and `ring` verifies the linear combination ([Linarith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html); [LinearCombination](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html)).
- See also: T48, T54, T59, T124

### T129 Presburger arithmetic
`prove` · stage: lean-tooling · signals: integers, congruence
aka: omega, lia, cutsat (deprecated), linear integer arithmetic, index arithmetic, parity side goals, modular side goals
- What: decides linear integer arithmetic: core `omega` over `Int`/`Nat` (including multiplication, `/` and `%` by constants) and grind's `lia` solver.
- Fits when: index arithmetic, parity and modular side goals.
- Lean: `omega` and `lia` produce kernel terms; use `lia`: the `cutsat` tactic is deprecated in v4.35.0 and its warning fails `--wfail`.
- Example: grind's `lia` procedure for linear integer arithmetic, formerly called cutsat ([grind](https://lean-lang.org/doc/reference/4.35.0/The--grind--tactic/)).
- See also: T21, T130

### T130 grind
`prove` · stage: lean-tooling · signals: identity, polynomial, integers
aka: SMT-style tactic, congruence closure, E-matching, case splits, ring solver, lia solver, grobner tactic, lemma instantiation
- What: SMT-style congruence closure, E-matching, case splits, a `lia` solver (formerly cutsat) and a ring solver; `grobner` runs only its Gröbner-basis solver.
- Fits when: goals that mix equalities, arithmetic and lemma instantiation.
- Lean: kernel terms.
- Example: produces "ordinary Lean proof terms for every fact it adds" ([grind](https://lean-lang.org/doc/reference/4.35.0/The--grind--tactic/)).
- See also: T20, T59, T129

### T131 Duper
`prove` · stage: lean-tooling
aka: superposition inside Lean, saturation prover, duper?, portfolioInstance, lean-auto backend, first-order goals
- What: a saturation prover inside Lean that outputs proof terms; `duper?` prints a faster call.
- Fits when: first-order goals over local facts.
- Lean: proof terms the kernel checks; it declares `axiom skSorryAx` internally (documented as removed from the final proof), so check `#print axioms` (T127).
- Example: the reconstruction backend for lean-auto ([Duper](https://github.com/leanprover-community/duper)).
- See also: T17, T127, T133

### T132 Aesop
`prove` · stage: lean-tooling
aka: white-box automation, best-first search, rule sets, safe and unsafe rules, normalisation rules, auto
- What: white-box best-first search over safe, unsafe and normalisation rules.
- Fits when: domain-specific closing tactics built from your own rule sets.
- Lean: kernel terms.
- Example: Lean 4's analogue of Isabelle's `auto` ([Aesop](https://github.com/leanprover-community/aesop)).
- See also: T130, T131

### T133 Hammers
`prove` · stage: lean-tooling
aka: LeanHammer, lean-auto, Sledgehammer, premise selection, neural premise selection, external provers, routine lemmas
- What: premise selection, translation, an external prover, proof reconstruction.
- Fits when: routine lemmas inside larger proofs.
- Lean: lean-auto reconstructs proofs only through Duper (T131); its SMT and TPTP calls have no reconstruction; always check axioms.
- Example: LeanHammer's neural premise selection solves 21% more goals than other Lean premise selectors ([LeanHammer](https://arxiv.org/abs/2506.07477); [lean-auto](https://github.com/leanprover-community/lean-auto); [survey](https://jfr.unibo.it/article/view/4593)).
- See also: T17, T131, T143

### T134 Type inhabitation search (Canonical)
`prove` · stage: lean-tooling
aka: Canonical, term search, dependent types, recursion, definitional equality, Natural Number Game
- What: searches for terms of a type, handling dependent types, recursion and definitional equality.
- Fits when: small dependently typed lemmas and programs.
- Lean: emits terms the kernel checks.
- Example: 84% of Natural Number Game problems in 51 s in total ([Norman–Avigad](https://arxiv.org/abs/2504.06239)).
- See also: T132

### T135 Lemma search
`prove` · stage: lean-tooling
aka: Loogle, exact?, Mathlib search, search by constant, subterm patterns, conclusion patterns
- What: finds Mathlib lemmas by constant, subterm pattern or conclusion.
- Fits when: every proof; avoids re-proving library facts.
- Lean: — (it only finds lemmas).
- Example: `|- tsum _ = _ * tsum _` style queries ([Loogle](https://loogle.lean-lang.org/)).
- See also: T143, T148

### T136 Property-based counterexample search
`prove` · stage: lean-tooling · signals: construction
aka: Plausible, QuickCheck, random testing, shrinking, misstatement detection, kill tests
- What: generates random instances of a statement's variables and shrinks failures, before any proof attempt.
- Fits when: every new Lean claim or definition; the cheapest kill test for a misstatement.
- Lean: a counterexample found is a witness; a pass proves nothing.
- Example: Plausible, property testing integrated into Lean 4's tactic framework ([GitHub: plausible](https://github.com/leanprover-community/plausible)); QuickCheck ([Wikipedia: QuickCheck](https://en.wikipedia.org/wiki/QuickCheck)).
- See also: T137, T146

### T137 Theory exploration
`prove` · stage: lean-tooling · signals: identity
aka: Hipster, QuickSpec, conjecture generation, lemma discovery, equational lemmas, basic lemma library
- What: enumerates small terms, conjectures equations that testing supports, proves and keeps the interesting ones as lemmas.
- Fits when: a new definition needs its basic lemma library.
- Lean: —
- Example: Hipster for Isabelle/HOL ([arXiv:1405.3426](https://arxiv.org/abs/1405.3426)).
- See also: T80, T136
