# Automated reasoning and decision procedures
First-order provers, model finders and decision procedures that run outside Lean; their answers need replay or a certificate.

### T17 Superposition provers
`prove` · stage: decide · signals: group, identity
aka: Vampire, E prover, Prover9, Otter, EQP, saturation, first-order logic with equality, equational logic, Robbins problem, Boolean algebra axioms
- What: first-order saturation with equality.
- Fits when: equational and first-order statements, such as algebraic laws.
- Lean: reconstruct with Duper (T131), or turn equational chains into `calc` proofs.
- Example: the Robbins problem, solved by EQP in 8 days on an RS/6000; Otter then turned it into a checked proof object ([McCune](https://www.cs.unm.edu/~mccune/papers/robbins/); [Vampire](https://vprover.github.io/)).
- See also: T18, T19, T20, T131, T133

### T18 Crowd plus automated provers at scale
`prove` `compute` · stage: decide · signals: group, identity, classification
aka: Equational Theories Project, ETP, implication grid, magma laws, universal algebra, collaborative formalization
- What: splits a huge implication grid; automated provers and finite models take the bulk, humans the rest, and Lean validates everything.
- Fits when: problem families with millions of small subquestions.
- Lean: many small files, checked in parallel (T122).
- Example: all 22,028,942 implications among 4,694 magma laws ([ETP](https://arxiv.org/abs/2512.07087)).
- See also: T17, T19, T122

### T19 Finite model finding
`find` `prove` · stage: decide · signals: group, logic, construction
aka: Mace4, Paradox, Vampire FMB, countermodels, counterexamples to implications, magmas, quasigroups, finite algebras
- What: searches for finite structures that satisfy axioms; finds counterexamples.
- Fits when: refuting implications in algebra and logic.
- Lean: a model is a finite operation table, so `decide` over `Fin n` checks the laws cheaply.
- Example: the ETP settled all implications among 4,694 magma laws, refuting the false ones mostly with finite models, all validated in Lean ([ETP](https://arxiv.org/abs/2512.07087); [Prover9/Mace4](https://www.cs.unm.edu/~mccune/prover9/)).
- See also: T14, T17, T18

### T20 Equality saturation (e-graphs)
`prove` · stage: decide · signals: identity, group
aka: egg, e-graph, rewriting to saturation, normal forms, term extraction, simplification
- What: applies all rewrites to an e-graph until saturation, then extracts the best equal term.
- Fits when: equational reasoning in algebraic structures, normal forms, simplification.
- Lean: —
- Example: egg ([arXiv:2004.03082](https://arxiv.org/abs/2004.03082); [Wikipedia: E-graph](https://en.wikipedia.org/wiki/E-graph)).
- See also: T17, T130

### T21 Walnut (automatic sequences)
`prove` · stage: decide · signals: sequence, additive, regular-structure
aka: automatic sequences, automatic sets, finite automata, decision procedure, combinatorics on words, sums of palindromes, additive bases
- What: a decision procedure for first-order properties of automatic words.
- Fits when: combinatorics on words; additive number theory over automatic sets.
- Lean: the final automaton is a certificate, checkable by `decide` on DFA products; the bridge from formula to automaton has to be formalized once (new work).
- Example: every natural number is a sum of at most 4 binary palindromes (optimal), with similar results for bases 3 and 4 ([Rajasekaran–Shallit–Smith](https://arxiv.org/abs/1706.10206); [Walnut](https://arxiv.org/abs/1603.06017)).
- See also: T129

### T22 Real quantifier elimination (CAD)
`prove` · stage: decide · signals: polynomial, inequality, geometry
aka: cylindrical algebraic decomposition, QEPCAD B, real closed fields, semialgebraic sets, sign-invariant cells, Kahan's ellipse problem
- What: eliminates quantifiers over ℝ through sign-invariant cells.
- Fits when: real-algebraic statements in few variables.
- Lean: Mathlib has no CAD; re-certify each cell by SOS (T54) or interval arithmetic (T64), or give `nlinarith` the hints.
- Example: Kahan's ellipse-in-circle problem (SIGSAM #9), the classic quantifier-elimination benchmark ([Paugam 1990](https://www.numdam.org/item/ITA_1990__24_2_161_0/); [QEPCAD B](https://www.usna.edu/Users/cs/wcbrown/qepcad/B/WhatisQEPCAD.html)).
- See also: T54, T64, T128

### T23 Termination by matrix interpretations
`prove` · stage: decide · signals: dynamics, computation, integers
aka: string rewriting, termination provers, natural and arctic matrix interpretations, ranking functions, Collatz conjecture, 3x+1
- What: finds matrices under which every rewrite rule decreases.
- Fits when: proving that a process always halts (Collatz-like maps, games, rewriting).
- Lean: the matrix inequality for each rule by `decide`; the general theorem formalized once.
- Example: Collatz as termination of a string rewriting system; nontrivial weakenings were proved automatically with natural and arctic matrix interpretations ([Yolcu–Aaronson–Heule](https://arxiv.org/abs/2105.14697)).
- See also: T58, T112
