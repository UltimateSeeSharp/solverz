# Experimental mathematics
Computing to guess (constants, closed forms, sequences, database patterns) and judging how far numerical evidence goes.

### T76 Integer relation detection (PSLQ)
`compute` `prove` · stage: explore · signals: analytic, identity, numeric-only
aka: PSLQ, integer relations, BBP formula, digit extraction, closed forms of constants, sums and integrals
- What: finds integers a with a·x ≈ 0 from high-precision values; a relation with n terms of d digits needs about n·d digits.
- Fits when: identifying constants; closed forms for sums and integrals.
- Lean: the relation is only a conjecture; prove it separately (telescoping, WZ); algebraic claims by exact polynomial arithmetic.
- Example: the BBP digit-extraction formula for π, found with PSLQ in 1996 ([Bailey](https://www.davidhbailey.com/dhbpapers/pslq-cse.pdf)).
- See also: T46, T77, T78, T83

### T77 Inverse symbolic calculators
`compute` · stage: explore · signals: analytic, identity, numeric-only
aka: RIES, mpmath identify, findpoly, recognizing constants, guessing minimal polynomials
- What: search formula space for a given number.
- Fits when: recognizing a computed constant, eigenvalue or limit.
- Lean: candidates only; an algebraic claim is checked with `norm_num`/`ring`.
- Example: `findpoly(1+√2, 2)` returns x²−2x−1 ([mpmath](https://mpmath.org/doc/current/identification.html); [RIES](https://www.mrob.com/pub/ries/index-3.html)).
- See also: T76

### T78 Ramanujan Machine
`compute` · stage: explore · signals: analytic, sequence, identity
aka: continued fractions, meet-in-the-middle, gradient descent, formulas for constants, π, ζ(3)
- What: meet-in-the-middle and gradient-descent search over continued fractions.
- Fits when: generating formulas for constants.
- Lean: conjectures only; finite convergent identities by `norm_num`.
- Example: new conjectured continued fractions, including ones for 24/π² and 8/(7ζ(3)) ([Raayoni et al.](https://arxiv.org/abs/1907.00205)).
- See also: T76

### T79 OEIS lookup
`compute` · stage: explore · signals: sequence, exact-value
aka: On-Line Encyclopedia of Integer Sequences, Superseeker, sequence identification, transforms of sequences
- What: 401,032 sequences, plus the Superseeker transform search.
- Fits when: the first step after computing any sequence.
- Lean: a match is evidence, not proof; small terms by `decide`.
- Example: SMS-based SAT enumeration verified and extended planar-graph sequences in the OEIS ([Kirchweger–Scheucher–Szeider](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.14); [OEIS](https://oeis.org/)).
- See also: T31, T62, T81

### T80 Automated conjecturing
`prove` · stage: explore · signals: graph, inequality
aka: Graffiti, TxGraffiti, Dalmatian heuristic, graph invariants, conjectured inequalities between invariants
- What: proposes inequalities between invariants from data tables, filtered by the Dalmatian heuristic.
- Fits when: generating conjectured bounds in graph theory and beyond.
- Lean: falsify on small graphs with `decide`, then prove.
- Example: TxGraffiti's conjectures led to several graph-theory publications ([Davila](https://arxiv.org/abs/2409.19379)).
- See also: T81, T86, T136

### T81 Curated databases
`find` `bound` · stage: explore · signals: graph, set-family, arithmetic-geometry, construction
aka: LMFDB, House of Graphs, La Jolla Covering Repository, LJCR, OEIS, best-known objects, current bounds, extremal examples, counterexamples, training data
- What: hold best-known objects, extremal examples and invariants.
- Fits when: seeds for find and bound problems; candidate counterexamples; training data.
- Lean: all database content is untrusted; re-check each object.
- Example: House of Graphs hosts complete graph lists and "interesting" graphs (extremal, counterexamples) ([HoG 2.0](https://arxiv.org/abs/2210.17253); [LMFDB](https://www.lmfdb.org/); [LJCR](https://dmgordon.org/covering-designs/)).
- See also: T79, T87, T90

### T82 Persistent homology
`compute` · stage: explore · signals: topology, geometry
aka: topological data analysis, barcodes, persistence, filtered complexes, point clouds, robust features
- What: computes barcodes of a filtered complex built from data; long bars are robust features, stable under perturbation.
- Fits when: point clouds of computed objects (configurations, embeddings, parameter spaces).
- Lean: —
- Example: barcodes and their stability ([Wikipedia: Persistent homology](https://en.wikipedia.org/wiki/Persistent_homology)).
- See also: T73

### T83 Independent high-precision cross-checks
`compute` `bound` · stage: explore · signals: analytic, numeric-only
aka: Hundred-digit Challenge, Trefethen, unrelated methods, method artefacts, digit agreement
- What: computes the same number by unrelated methods to many digits; agreement separates truth from method artefacts.
- Fits when: a constant will be targeted by a bound or recognized by PSLQ.
- Lean: —
- Example: Trefethen's SIAM 100-digit challenge: 20 teams got all ten problems to the required ten digits ([Wikipedia: Hundred-dollar, Hundred-digit Challenge problems](https://en.wikipedia.org/wiki/Hundred-dollar,_Hundred-digit_Challenge_problems)).
- See also: T64, T76, T84

### T84 Conditioning and backward error
`find` `prove` `bound` `compute` · stage: explore · signals: polynomial, matrix, numeric-only
aka: condition number, backward error analysis, Wilkinson's polynomial, ill-conditioning, numerical stability, near-ties, floating-point evidence
- What: estimates how much the answer moves under input perturbations before floating-point evidence is trusted.
- Fits when: deciding whether a numerical root, eigenvalue or near-tie is evidence or noise.
- Lean: —
- Example: Wilkinson's polynomial ∏(x − i): tiny coefficient changes move the roots far ([Wikipedia: Wilkinson's polynomial](https://en.wikipedia.org/wiki/Wilkinson%27s_polynomial); [Wikipedia: Condition number](https://en.wikipedia.org/wiki/Condition_number)).
- See also: T64, T83

### T85 Numerical continuation and bifurcation tracking
`find` · stage: explore · signals: dynamics, pde, analytic
aka: pseudo-arclength continuation, AUTO, MATCONT, bifurcation diagrams, folds, branch points, branch switching, solution branches
- What: follows a solution branch in a parameter (pseudo-arclength), detects folds and branch points, switches branches.
- Fits when: a family of solutions where the wanted object sits on a branch from a known one.
- Lean: —
- Example: pseudo-arclength continuation and tools such as AUTO and MATCONT ([Wikipedia: Numerical continuation](https://en.wikipedia.org/wiki/Numerical_continuation)).
- See also: T68, T69
