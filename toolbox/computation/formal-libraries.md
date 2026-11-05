# Formal libraries and infrastructure
Libraries, statement collections and planning tools around Lean proofs.

### T148 Mathlib
`prove` `find` `bound` `compute` · stage: lean-tooling
aka: Lean mathematical library, Mathlib4, library lemmas, definitions and theorems
- What: about 140k definitions and 292k theorems.
- Fits when: the base of every statement and proof.
- Lean: native.
- Example: the foundation of the Lean-verified flag-algebra work ([stats](https://leanprover-community.github.io/mathlib_stats.html); [Formalizing flag algebras](https://arxiv.org/abs/2607.23500)).
- See also: T135, T150

### T149 Isabelle Archive of Formal Proofs
`prove` · stage: lean-tooling
aka: AFP, Isabelle/HOL, formalized developments, precedents for formalizing computations
- What: a journal-style library of checked Isabelle developments.
- Fits when: precedents and proof ideas for formalizing computations.
- Lean: port the ideas; the proofs themselves don't transfer.
- Example: a journal-style archive of Isabelle developments, indexed by dblp ([AFP](https://www.isa-afp.org/)).
- See also: T11, T65

### T150 Blueprints
`prove` · stage: lean-tooling
aka: leanblueprint, dependency graph, LaTeX plan, status colours, Sphere Eversion Project, project planning, agent coordination
- What: a LaTeX plan linked to Lean declarations, with a dependency graph and status colours.
- Fits when: multi-step proofs and agent coordination.
- Lean: `checkdecls` checks that every referenced declaration exists.
- Example: began with the Sphere Eversion Project in 2020 ([leanblueprint](https://github.com/PatrickMassot/leanblueprint); [checkdecls](https://github.com/PatrickMassot/checkdecls)).
- See also: T148

### T151 Formal Conjectures
`prove` · stage: lean-tooling
aka: google-deepmind formal-conjectures, open conjectures in Lean, statement benchmark, autoformalization benchmark
- What: Lean statements of open conjectures, tagged by category.
- Fits when: ready-made statements, to compare against (not to trust).
- Lean: audit every statement before use, since misstatements occur.
- Example: a benchmark for provers and autoformalization; it tracks monthly Mathlib releases ([formal-conjectures](https://github.com/google-deepmind/formal-conjectures)).
- See also: T146, T148
