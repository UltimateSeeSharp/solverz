# Semidefinite and sum-of-squares relaxations
SDP bounds, SOS and Positivstellensatz certificates, flag algebras and moment hierarchies.

### T53 SDP bounds for codes and packings
`bound` · stage: relax · signals: geometry, set-family, inequality
aka: Schrijver's SDP bound, Bachoc–Vallentin, three-point bounds, kissing numbers, spherical codes, binary codes, semidefinite programming
- What: three-point semidefinite programs for codes on the sphere.
- Fits when: kissing numbers and codes where LP is too weak.
- Lean: round the dual to rationals; show PSD by an exact LDLᵀ with nonnegative pivots, then check the identity with `ring`.
- Example: SDP kissing bounds that recover the known values in dimensions 3, 4, 8 and 24 ([Bachoc–Vallentin](https://arxiv.org/abs/math/0608426)).
- See also: T50, T54, T124

### T54 Sums of squares and Positivstellensatz
`prove` `bound` · stage: relax · signals: polynomial, inequality, impossibility
aka: SOS, sum-of-squares hierarchy, Positivstellensatz certificate, Gram matrix, LMI, semialgebraic sets, polynomial inequalities, nonnegative polynomials, Lyapunov functions
- What: an SOS decomposition is an LMI, and Positivstellensatz certificates prove semialgebraic sets empty.
- Fits when: polynomial inequalities, empty semialgebraic sets, Lyapunov functions.
- Lean: p = Σ cᵢqᵢ² with rational cᵢ ≥ 0, checked by `ring` plus `positivity`; or pass the squares as hints to `nlinarith`.
- Example: HOL Light verifies nonlinear real formulas from SOS certificates found numerically, with simple checking in a foundational prover ([Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/sos.html); [Parrilo thesis](https://www.mit.edu/%7Eparrilo/pubs/files/Thesis_abstract.html)).
- See also: T56, T58, T60, T124, T128

### T55 Flag algebras
`bound` `prove` · stage: relax · signals: graph, dense, inequality, asymptotic
aka: Razborov's flag algebras, subgraph densities, Turán density, inducibility, hypergraph Turán problems, five-cycles in triangle-free graphs, Erdős pentagon problem, π(C₅;K₃)=24/625
- What: a calculus on subgraph densities; SDP over flags gives asymptotic density bounds.
- Fits when: Turán-type densities, inducibility, hypergraph extremal problems.
- Lean: done in Lean 4 with standard axioms only; the SDP output is only candidate data and Lean checks every fact (that PSD is checked exactly over ℚ is unverified).
- Example: triangle-free graphs have at most (n/5)^5 five-cycles, settling a 1984 Erdős conjecture ([Hatami et al.](https://arxiv.org/abs/1102.1634)); Fisher's triangle-density result, with a new simple proof ([Razborov](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/flag-algebras/56DA1073B314D02783F7A4E074EAE6E5)); 7 Turán-type bounds in Lean 4, including π(C₅;K₃)=24/625 ([Formalizing flag algebras](https://arxiv.org/abs/2607.23500); [local flag algebras](https://arxiv.org/abs/2607.12461)).
- See also: T52, T53, T54, T124

### T56 Moment relaxations with solution extraction
`find` `bound` · stage: relax · signals: polynomial, inequality, construction
aka: Lasserre hierarchy, moment matrix, pseudo-moments, flat extension, GloptiPoly, polynomial optimization, extracting optimizers
- What: the dual side of the sum-of-squares hierarchy works with pseudo-moments; when the moment matrix is flat, the optimizers themselves can be read off.
- Fits when: a polynomial optimization problem where the optimal point (the object to find), not just the value, is wanted.
- Lean: —
- Example: the Lasserre hierarchy and GloptiPoly for the moment side ([Wikipedia: Sum-of-squares optimization](https://en.wikipedia.org/wiki/Sum-of-squares_optimization)).
- See also: T54

### T57 Copositive reformulation
`bound` · stage: relax · signals: graph, matrix, inequality
aka: copositive cone, completely positive, stability number, independence number, clique bounds, de Klerk–Pasechnik hierarchy, quadratic programs over the simplex
- What: many NP-hard quadratic and combinatorial optima are exactly linear programs over the copositive cone; inner approximations by LP or SDP give convergent hierarchies of bounds.
- Fits when: stability numbers, clique bounds, quadratic programs over the simplex.
- Lean: —
- Example: de Klerk–Pasechnik's SDP hierarchy for the stability number from its copositive formulation, studied by Laurent–Vargas ([arXiv:2103.01574](https://arxiv.org/abs/2103.01574); [Wikipedia: Copositive matrix](https://en.wikipedia.org/wiki/Copositive_matrix)).
- See also: T51, T53

### T58 Lyapunov and ranking-function synthesis by SDP
`prove` · stage: relax · signals: dynamics, polynomial, inequality
aka: Lyapunov functions, ranking functions, potential functions, stability, termination, SOS programming
- What: SOS programs produce a function that decreases along the dynamics.
- Fits when: stability, termination, potential-function arguments.
- Lean: the decrease condition, checked by a rational SOS (T54).
- Example: Lyapunov function computation is an application in the Parrilo thesis ([Parrilo](https://www.mit.edu/%7Eparrilo/pubs/files/Thesis_abstract.html)).
- See also: T23, T54, T103, T112
