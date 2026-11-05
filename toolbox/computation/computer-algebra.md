# Computer algebra
Exact symbolic computation whose output (cofactors, recurrences, coset tables) becomes a Lean-checkable certificate.

### T59 Gröbner bases and BKK root counts
`prove` `compute` · stage: algebra · signals: polynomial, identity
aka: Gröbner basis, elimination, ideal membership, cofactors, mixed volume, BKK bound, polynomial systems, finiteness of solutions, relative equilibria, n-body problem
- What: canonical ideal bases; mixed volumes bound the number of solutions.
- Fits when: polynomial systems (finiteness, elimination, ideal membership).
- Lean: give the cofactors to `linear_combination` (checked by `ring1`); core's `grobner` tactic (grind's Gröbner solver) also works; `polyrith` is dead (its Sage server shut down).
- Example: finiteness of relative equilibria in the Newtonian 4-body problem ([Hampton–Moeckel](https://homepages.math.uic.edu/~jan/solving_talks/marshall_hampton.html); [LinearCombination](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html); [Polyrith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html)).
- See also: T60, T69, T130

### T60 Nullstellensatz certificates
`prove` · stage: algebra · signals: polynomial, colouring, impossibility
aka: Hilbert's Nullstellensatz, NulLA, 1 = Σ cᵢfᵢ, polynomial calculus, algebraic proof systems, non-3-colourability, matchings, infeasible polynomial systems
- What: a polynomial system has no solution iff 1 = Σ cᵢfᵢ; the cᵢ are found by linear algebra in low degree.
- Fits when: combinatorial non-existence encoded as polynomials (colourings, matchings).
- Lean: `linear_combination` with the cofactors cᵢ; low degree keeps the certificate small.
- Example: non-3-colourability of graphs with thousands of vertices ([De Loera et al.](https://arxiv.org/abs/0801.3788)).
- See also: T48, T54, T59

### T61 Creative telescoping and WZ pairs
`prove` · stage: algebra · signals: identity, sequence
aka: Wilf–Zeilberger pairs, WZ method, holonomic functions, HolonomicFunctions, recurrence certificates, hypergeometric sums, binomial-sum identities, q-TSPP, Gessel's lattice-path conjecture, WZ-LLM
- What: computes recurrences or ODEs for sums and integrals with rational certificates; a WZ pair's rational R(n,k) turns a hypergeometric identity into a telescoping sum.
- Fits when: identities for definite hypergeometric or holonomic sums and integrals; binomial-sum identities.
- Lean: check F(n+1,k)−F(n,k) = G(n,k+1)−G(n,k) by `field_simp; ring`, plus the boundary terms; large certificates stress `ring`.
- Example: Σₖ(−1)ᵏC(n,k)C(2k,k)4ⁿ⁻ᵏ = C(2n,n), with R = (2k−1)/(2n+1) ([WZ pair](https://en.wikipedia.org/wiki/Wilf%E2%80%93Zeilberger_pair)); the q-TSPP conjecture ([Koutschan–Kauers–Zeilberger](https://arxiv.org/abs/1002.4384)); Gessel's conjecture by a fully rigorous computer-aided proof ([Kauers–Koutschan–Zeilberger](https://arxiv.org/abs/0806.4300)); WZ-LLM turns WZ plans into Lean 4 sketches and proves 34% of 100 classic identities ([WZ-LLM](https://arxiv.org/abs/2605.04472)).
- See also: T48, T62, T76

### T62 Guess and prove for sequences
`compute` `prove` · stage: explore · signals: sequence, identity
aka: gfun, guessing, holonomic recurrences, P-recursive, D-finite, algebraic generating functions, closed forms, Catalan numbers
- What: fits a recurrence, ODE or algebraic equation to initial terms; the result is a conjecture until proved.
- Fits when: sequences from enumeration; compute problems that need a closed form.
- Lean: finitely many terms by `decide`; the general case needs a proof (closure properties, a bijection, or WZ).
- Example: twelve Catalan numbers are enough to guess (n+2)u(n+1) = 2(2n+1)u(n) ([gfun](https://perso.ens-lyon.fr/bruno.salvy/software/the-gfun-package/)).
- See also: T61, T79

### T63 Coset enumeration and Knuth–Bendix
`prove` `compute` · stage: algebra · signals: group, exact-value
aka: Todd–Coxeter, finitely presented groups, presentations of the trivial group, rewriting systems, completion, word problem, group order
- What: enumerates cosets of a finitely presented group, or completes a rewriting system.
- Fits when: showing a presentation is finite or trivial; word problems.
- Lean: a closed coset table is a certificate; check that every relator fixes every coset with `decide` (small tables).
- Example: Neumann's hard presentations of the trivial group turn out easy after experimentation ([Havas–Ramsay](https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/proving-a-group-trivial-made-easy-a-case-study-in-coset-enumeration/F3E807104814C7CB77A8F8339A6542C7)).
- See also: T29, T105
