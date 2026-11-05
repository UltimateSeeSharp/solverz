# Relaxations, rounding and decomposition
Operations-research tools: rounding fractional solutions, column generation, Lagrangian and Benders decomposition, matroid intersection, submodular selection, polyhedral computation.

### T1076 Randomized rounding
`find` `bound` · stage: relax · signals: graph, random, construction
aka: rounding fractional solutions, vector solutions, hyperplane rounding, Goemans–Williamson, Max-Cut, LP rounding, SDP rounding, good starting objects
- What: turns a fractional or vector solution into an integral one with bounded loss.
- Fits when: good starting objects for find or bound searches.
- Lean: the rounded object by `decide`.
- Example: Goemans–Williamson hyperplane rounding ([Wikipedia: Maximum cut](https://en.wikipedia.org/wiki/Maximum_cut)).
- See also: T1004, T1071, T1062

### T1077 Half-integrality
`find` `bound` · stage: relax · signals: graph
aka: half-integral LP optimum, values in {0, 1/2, 1}, Nemhauser–Trotter, vertex cover, LP kernel, 2k kernel, fixed variables, preprocessing, covering problems
- What: the LP optimum takes values in {0, 1/2, 1}; the variables it fixes shrink the instance.
- Fits when: vertex-cover-like covering problems; preprocessing before exact search.
- Lean: the LP bound by a rational dual (T48).
- Example: the Nemhauser–Trotter 2k kernel ([Wikipedia: Kernelization](https://en.wikipedia.org/wiki/Kernelization)).
- See also: T1124, T48

### T1078 Column generation
`bound` `compute` · stage: relax · signals: graph, set-family, inequality
aka: branch-and-price, pricing subproblem, negative reduced cost, exponentially many columns, configurations as variables, fractional chromatic number, covering numbers, cutting-stock problem
- What: solves an LP with exponentially many columns by pricing: a subproblem either finds a column of negative reduced cost or proves none exists.
- Fits when: the variables are configurations (independent sets, packing patterns), as for fractional chromatic and covering numbers.
- Lean: the final dual is a rational certificate (T48); checking it means checking every column's constraint, which is the pricing problem done in Lean.
- Example: the cutting-stock problem ([Wikipedia: Column generation](https://en.wikipedia.org/wiki/Column_generation)).
- See also: T48, T49

### T1079 Lagrangian relaxation
`bound` · stage: relax · signals: inequality
aka: Lagrange multipliers, multiplier vector, subgradient optimization, coupling constraints, Lagrangian bound, decomposition
- What: moves the hard constraints into the objective with multipliers; every multiplier vector gives a bound, and subgradient steps tighten it.
- Fits when: a few coupling constraints spoil an otherwise easy problem.
- Lean: fix rational multipliers; the bound is then the exact optimum of the relaxed, easy problem.
- Example: the relaxed solution bounds the optimum for any fixed multipliers ([Wikipedia: Lagrangian relaxation](https://en.wikipedia.org/wiki/Lagrangian_relaxation)).
- See also: T51, T48

### T1080 Benders decomposition
`compute` `bound` · stage: search · signals: local-constraints
aka: logic-based Benders, master problem, subproblem, Benders cuts, combinatorial core plus easy remainder, LP or SAT subproblems
- What: fixes the master variables, solves the subproblem, returns a cut that excludes the master choice, and repeats.
- Fits when: a hard combinatorial core plus an easy remainder (an LP, a SAT call or a check per case).
- Lean: each cut is justified by its subproblem's certificate (T48 or T5).
- Example: a master problem over the first set of variables with cuts from the second ([Wikipedia: Benders decomposition](https://en.wikipedia.org/wiki/Benders_decomposition)).
- See also: T8, T110

### T1081 Matroid intersection
`prove` `compute` · stage: search · signals: set-family, graph, exact-value
aka: Edmonds, common independent set, matroid rank, min–max theorem, bipartite matching, rainbow spanning trees, arborescences, common basis
- What: the largest common independent set of two matroids equals a minimum over rank sums; polynomial algorithms return both the set and the min–max certificate.
- Fits when: the object is a common basis of two matroids (bipartite matchings, rainbow spanning trees, arborescences).
- Lean: the set and its rank-sum certificate on small ground sets by `decide`; Mathlib has matroids (`Mathlib/Combinatorics/Matroid`) and Hall's theorem for bipartite graphs (`Mathlib/Combinatorics/SimpleGraph/Hall.lean`).
- Example: Edmonds's matroid intersection theorem ([Wikipedia: Matroid intersection](https://en.wikipedia.org/wiki/Matroid_intersection)).
- See also: T1108

### T1082 Submodular maximization
`find` · stage: search · signals: set-family
aka: diminishing returns, greedy 1 − 1/e guarantee, Lovász extension, maximum coverage, budgeted selection, choosing test instances, cubes, seeds or lemmas
- What: diminishing-returns objectives admit greedy (1 − 1/e) guarantees and convex Lovász extensions.
- Fits when: picking a budgeted set (test instances, cubes, seeds, lemmas) to maximize coverage.
- Lean: —
- Example: maximum coverage is the special case ([Wikipedia: Submodular set function](https://en.wikipedia.org/wiki/Submodular_set_function)).
- See also: T1351

### T1083 Polyhedral computation
`compute` · stage: algebra · signals: geometry, inequality
aka: Fourier–Motzkin elimination, double description, vertex enumeration, facet enumeration, convex hull, projection of polyhedra, reverse search, Avis–Fukuda, correlation polytope, cut polytope, flag-algebra regions
- What: projects polyhedra and converts between vertex and facet descriptions.
- Fits when: the answer is a polytope's facets or vertices (correlation and cut polytopes, flag-algebra regions).
- Lean: vertex and facet lists are rational data, each incidence checked by `norm_num` or `decide`; completeness of a list needs its own argument.
- Example: Avis–Fukuda reverse-search vertex enumeration ([Wikipedia: Vertex enumeration problem](https://en.wikipedia.org/wiki/Vertex_enumeration_problem)); Farkas' lemma by Fourier–Motzkin elimination ([Wikipedia: Fourier–Motzkin elimination](https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination)).
- See also: T48, T128, T1089
