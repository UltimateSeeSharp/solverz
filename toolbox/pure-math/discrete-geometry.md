# Discrete and convex geometry
Convexity theorems, incidences and drawings, rigidity, dissections, lattice points, tilings and lattice packings.

### T735 Helly, Radon and Carathéodory
`prove` · stage: argue · signals: geometry
aka: Helly's theorem, Radon partition, Carathéodory's theorem, colourful Carathéodory (Bárány), colourful Helly, piercing numbers, LP-type problems, intersection patterns of convex sets
- What: in R^d, d+1 points control convex hulls and d+1-wise intersections control the whole family.
- Fits when: finite-dimensional convexity, piercing, LP-type problems.
- Lean: Mathlib: `Convex.radon_partition`, `Convex.helly_theorem` (and compact variants), `convexHull_eq_union` (Carathéodory).
- Example: Helly's theorem; Bárány's colourful Carathéodory theorem ([Wikipedia: Helly's theorem](https://en.wikipedia.org/wiki/Helly's_theorem), [Wikipedia: Radon's theorem](https://en.wikipedia.org/wiki/Radon's_theorem), [Wikipedia: Carathéodory's theorem](https://en.wikipedia.org/wiki/Carathéodory's_theorem_%28convex_hull%29)).
- See also: T736, T722

### T736 Tverberg partitions and centerpoints
`prove` · stage: argue · signals: geometry
aka: Tverberg's theorem, centerpoint theorem, Tukey depth, ham-sandwich-type depth, topological Tverberg
- What: (r−1)(d+1)+1 points in R^d split into r parts whose hulls share a point; deep points exist.
- Fits when: depth and partition problems.
- Lean: Mathlib has Radon (r = 2, `Convex.radon_partition`); Tverberg for general r is not there.
- Example: Tverberg's theorem; centerpoint theorem ([Wikipedia: Tverberg's theorem](https://en.wikipedia.org/wiki/Tverberg's_theorem), [Wikipedia: Centerpoint](https://en.wikipedia.org/wiki/Centerpoint_%28geometry%29)).
- See also: T735, T711

### T737 Positive-fraction Ramsey geometry
`prove` `bound` · stage: argue · signals: geometry, colouring, asymptotic
aka: cups and caps, Erdős–Szekeres, happy ending problem, convex position, positive-fraction Erdős–Szekeres, transversal structures
- What: finds points in convex position through cups/caps and positive-fraction transversal structures.
- Fits when: Erdős–Szekeres-type problems.
- Lean: small cases by SAT with a verified encoding (T11); the asymptotic argument by hand.
- Example: Suk's near-optimal Erdős–Szekeres bound 2^{n+o(n)} ([arXiv:1604.08657](https://arxiv.org/abs/1604.08657), [Wikipedia: Happy ending problem](https://en.wikipedia.org/wiki/Happy_ending_problem)).
- See also: T11, T735

### T738 Crossing number inequality
`prove` `bound` · stage: argue · signals: graph, geometry, inequality
aka: crossing lemma, Ajtai–Chvátal–Newborn–Szemerédi, Leighton, Székely's method, incidence bounds via drawings, Szemerédi–Trotter
- What: a drawing of a graph with many edges for its vertices has many crossings.
- Fits when: incidence bounds via graph drawings.
- Lean: —
- Example: Székely's proof of the Szemerédi–Trotter theorem ([Wikipedia: Crossing number inequality](https://en.wikipedia.org/wiki/Crossing_number_inequality), [Wikipedia: Szemerédi–Trotter theorem](https://en.wikipedia.org/wiki/Szemerédi–Trotter_theorem)).
- See also: T739, T396

### T739 Elekes–Sharir framework
`bound` · stage: reformulate · signals: geometry, asymptotic
aka: distinct distances, rigid motions, line incidences in R^3, Guth–Katz, Erdős distinct distances problem
- What: turns distance problems into incidences of lines in R^3 through rigid motions.
- Fits when: distinct distances and similar problems.
- Lean: —
- Example: Guth–Katz N/log N distinct distances ([arXiv:1011.4105](https://arxiv.org/abs/1011.4105), [Wikipedia: Erdős distinct distances problem](https://en.wikipedia.org/wiki/Erdős_distinct_distances_problem)).
- See also: T396, T738

### T740 ε-nets and VC dimension
`prove` `bound` · stage: argue · signals: geometry, set-family, random
aka: epsilon-net theorem, Haussler–Welzl, range spaces, VC dimension, shatter function, geometric set cover, hitting sets, transversals
- What: in a range space of bounded VC dimension, a small random sample hits every large range.
- Fits when: geometric set cover, transversals.
- Lean: Mathlib has VC dimension and shattering (`Finset.vcDim`, `Finset.Shatters`, `Finset.card_shatterer_le_sum_vcDim`); the ε-net theorem is not there.
- Example: the ε-net theorem for range spaces of bounded VC dimension ([Wikipedia: ε-net (computational geometry)](https://en.wikipedia.org/wiki/Ε-net_%28computational_geometry%29)).
- See also: T371, T33

### T741 Linear-algebra bounds in geometry
`prove` `bound` · stage: argue · signals: geometry, matrix, set-family, colouring
aka: Frankl–Wilson in geometry, Borsuk's conjecture, chromatic number of R^n, diameter graphs, two-distance sets, polynomial dimension bounds
- What: Frankl–Wilson-type intersection bounds applied to colouring and diameter problems in R^n.
- Fits when: high-dimensional geometric colourings.
- Lean: the dimension bound by Mathlib linear algebra (`LinearIndependent`, `Module.finrank`); the specific vectors by `decide +kernel`.
- Example: Borsuk's conjecture fails (Kahn–Kalai) ([arXiv:math/9307229](https://arxiv.org/abs/math/9307229), [Wikipedia: Borsuk's conjecture](https://en.wikipedia.org/wiki/Borsuk's_conjecture)).
- See also: T398, T399

### T742 Rigidity theory
`prove` · stage: argue · signals: geometry, graph, matrix
aka: Cauchy's rigidity theorem, Laman graphs, generic rigidity, self-stresses, infinitesimal rigidity, rigidity matrix, frameworks, polyhedra, Maxwell counting
- What: counts degrees of freedom; stresses certify rigidity or flexibility.
- Fits when: frameworks and polyhedra.
- Lean: infinitesimal rigidity of one framework is a rank statement on its rigidity matrix, checkable over ℚ by `decide +kernel` or `norm_num`.
- Example: Cauchy's rigidity theorem for convex polyhedra; Laman's characterization of generic planar rigidity ([Wikipedia: Cauchy's theorem (geometry)](https://en.wikipedia.org/wiki/Cauchy's_theorem_%28geometry%29), [Wikipedia: Laman graph](https://en.wikipedia.org/wiki/Laman_graph)).
- See also: T743

### T743 Realization theorems
`prove` `find` · stage: construct · signals: geometry, graph, construction
aka: Steinitz's theorem, Koebe–Andreev–Thurston, circle packing theorem, coin graphs, polytope realizability, planar graph representations
- What: a combinatorial type is realized geometrically, often with extra structure (circles, rational coordinates).
- Fits when: polytope realizability, planar graph representations.
- Lean: a concrete realization with rational coordinates is checked by `norm_num`/`decide +kernel`; the general theorems are not in Mathlib.
- Example: Steinitz's theorem; the circle packing theorem ([Wikipedia: Steinitz's theorem](https://en.wikipedia.org/wiki/Steinitz's_theorem), [Wikipedia: Circle packing theorem](https://en.wikipedia.org/wiki/Circle_packing_theorem)).
- See also: T742, T735

### T744 Scissors-congruence invariants
`prove` · stage: argue · signals: geometry, impossibility
aka: Dehn invariant, Hilbert's third problem, equidecomposability, dissections, additive invariants beyond volume
- What: an additive invariant beyond volume obstructs a dissection.
- Fits when: dissection and equidecomposability questions.
- Lean: —
- Example: Dehn's solution of Hilbert's third problem ([Wikipedia: Hilbert's third problem](https://en.wikipedia.org/wiki/Hilbert's_third_problem)).
- See also: T745, T329

### T745 Valuation colouring arguments
`prove` · stage: argue · signals: geometry, colouring, impossibility, parity
aka: Monsky's theorem, 2-adic valuation, Sperner colouring of the plane, equal-area triangulations, equidissection
- What: extends a p-adic valuation to R and colours the plane by it; Sperner's lemma finds a forbidden triangle.
- Fits when: dissection into triangles or simplices of equal area.
- Lean: —
- Example: Monsky's theorem: no square splits into an odd number of equal-area triangles ([Wikipedia: Monsky's theorem](https://en.wikipedia.org/wiki/Monsky's_theorem)).
- See also: T708, T744

### T746 Mixed volumes and Alexandrov–Fenchel
`prove` `bound` · stage: argue · signals: geometry, inequality, sequence
aka: Alexandrov–Fenchel inequality, mixed volumes, log-concavity, van der Waerden permanent conjecture, Egorychev–Falikman
- What: mixed volumes are log-concave; realize a sequence as mixed volumes to get its log-concavity.
- Fits when: log-concavity of combinatorial sequences realized as mixed volumes.
- Lean: —
- Example: the Alexandrov–Fenchel inequality; Egorychev's proof of van der Waerden's permanent conjecture ([Wikipedia: Mixed volume](https://en.wikipedia.org/wiki/Mixed_volume), [Wikipedia: Permanent](https://en.wikipedia.org/wiki/Permanent_%28mathematics%29)).
- See also: T405, T611

### T747 Lattice-point counting
`compute` `prove` · stage: argue · signals: geometry, integers, exact-value
aka: Pick's theorem, Ehrhart polynomial, Ehrhart quasi-polynomial, integer points in dilated polytopes, counting lattice points
- What: counts lattice points in polytopes by polynomial formulas in the dilation factor.
- Fits when: integer points in dilated polytopes.
- Lean: a single count by `decide +kernel` over a box; Pick and Ehrhart are not in Mathlib.
- Example: Pick's theorem; Ehrhart polynomials ([Wikipedia: Pick's theorem](https://en.wikipedia.org/wiki/Pick's_theorem), [Wikipedia: Ehrhart polynomial](https://en.wikipedia.org/wiki/Ehrhart_polynomial)).
- See also: T460, T527

### T748 Group-ring factorization for tilings
`prove` · stage: reformulate · signals: geometry, group, product-structure
aka: Hajós's theorem, Minkowski's conjecture on cube tilings, factorization of finite abelian groups, lattice tilings, Keller's conjecture
- What: a lattice tiling becomes a factorization of a finite abelian group into subsets; group rings decide it.
- Fits when: cube tilings, factorization problems.
- Lean: a given factorization A + B = G of a finite group is checked by `decide +kernel`.
- Example: Hajós's proof of Minkowski's conjecture on lattice cube tilings ([Wikipedia: Hajós's theorem](https://en.wikipedia.org/wiki/Hajós's_theorem)).
- See also: T437, T6

### T749 Averaging over lattices
`bound` `find` · stage: argue · signals: geometry, random, construction
aka: Minkowski–Hlawka theorem, Siegel mean value theorem, random lattices, lattice packings, packing density lower bounds
- What: the average lattice has few short vectors, so a good lattice exists.
- Fits when: lower bounds for packing densities.
- Lean: —
- Example: the Minkowski–Hlawka theorem ([Wikipedia: Minkowski–Hlawka theorem](https://en.wikipedia.org/wiki/Minkowski–Hlawka_theorem)).
- See also: T527, T50, T53

### T750 Besicovitch-type constructions
`find` · stage: construct · signals: geometry, analytic, construction
aka: Kakeya sets, Besicovitch sets, Perron trees, sliding triangles, measure-zero sets with segments in all directions
- What: tiny sets containing segments in all directions via iterated sliding of triangles.
- Fits when: counterexamples to intuitive measure statements.
- Lean: —
- Example: Besicovitch's measure-zero Kakeya sets ([Wikipedia: Kakeya set](https://en.wikipedia.org/wiki/Kakeya_set)).
- See also: T640, T393

### T838 Spindles and the d-step lift
`find` · stage: construct · signals: geometry, construction
aka: Hirsch conjecture, polytope diameter, spindles, prismatoids, strong d-step theorem, Klee–Walkup d-step conjecture, Santos, low-dimensional counterexample lifted to high dimension
- What: a d-spindle has two vertices such that every facet contains exactly one, its length the distance between them; one with n facets and length l lifts to an (n − d)-spindle with 2n − 2d facets and length at least l + n − 2d, so a spindle with l > d becomes a counterexample to the d-step and Hirsch bounds.
- Fits when: a diameter or distance bound for polytopes (or another family with a lifting theorem) must be broken; search for the violation in low dimension, where computation is cheap, and let the lifting theorem carry it up.
- Lean: the low-dimensional spindle is a finite rational object, its facets, vertices and graph distance exact computations for a kernel-checked witness (T118); the lifting theorem needs its own proof; Mathlib has exposed faces (`IsExposed`) but no polytope graphs.
- Example: Santos built a 5-dimensional spindle of length 6 with 48 facets and lifted it to a 43-dimensional polytope with 86 facets and diameter above 43 ([Wikipedia: Hirsch conjecture](https://en.wikipedia.org/wiki/Hirsch_conjecture), [arXiv:1006.2814](https://arxiv.org/abs/1006.2814)); Matschke–Santos–Weibel found 5-prismatoids of width 6 with 25 vertices instead of 48, giving counterexamples in dimension 20 ([arXiv:1202.4701](https://arxiv.org/abs/1202.4701)).
- See also: T1370, T743, T300

### T839 Forced hierarchy: metatiles and substitution
`prove` `find` · stage: argue · signals: geometry, regular-structure, impossibility
aka: aperiodic tilings, aperiodic monotile, einstein problem, hat, spectre, metatiles, substitution tilings, inflation, deflation, composition, hierarchical tilings, matching rules, Penrose tiling, Robinson tiles, Goodman-Strauss, domino problem
- What: shows that every tiling by the given tiles groups into larger clusters (metatiles) that tile by the same rule again, at every scale; the forced infinite hierarchy rules out a period, and a substitution rule on the metatiles shows that a tiling exists.
- Fits when: a tile set should tile only non-periodically, or local rules should force global structure; find clusters that behave like a substitution system, then prove every tiling decomposes into them.
- Lean: the combinatorial step is a finite enumeration of legal neighbourhoods and compositions, a candidate for a kernel-checked case split (T122); Mathlib has protosets and discrete tiles (`Mathlib/Combinatorics/Tiling/Tile.lean`) but no substitution or aperiodicity theory.
- Example: the hat: metatiles with substitution rules show it tiles, a computer-assisted combinatorial proof forces hierarchical, hence aperiodic, tilings, and a geometric incommensurability argument covers generic members of its shape family ([arXiv:2303.10798](https://arxiv.org/abs/2303.10798)); Penrose tiles split into smaller copies under deflation, and matching rules force the substitution ([Wikipedia: Penrose tiling](https://en.wikipedia.org/wiki/Penrose_tiling)); most known aperiodic sets work by forcing a non-periodic hierarchy ([Wikipedia: Aperiodic set of prototiles](https://en.wikipedia.org/wiki/Aperiodic_set_of_prototiles)).
- See also: T1366, T748, T122
