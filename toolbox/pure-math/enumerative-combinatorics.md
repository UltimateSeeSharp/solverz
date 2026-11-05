# Enumerative and algebraic combinatorics
Generating functions and their asymptotics, inversion formulas, counting up to symmetry, bijections, q-series, and algebra that constrains face numbers.

### T447 Symbolic method
`compute` `prove` · stage: argue · signals: sequence, exact-value
aka: generating functions, ordinary and exponential generating functions, OGF, EGF, admissible constructions, SEQ SET CYC, Flajolet–Sedgewick, recursively defined families, trees, words, compositions
- What: translates constructions (sequence, set, cycle) into operations on generating functions.
- Fits when: a family is defined recursively from smaller pieces.
- Lean: Mathlib `PowerSeries`; Catalan numbers with `card_dyckWord_semilength_eq_catalan`; single coefficients by `decide +kernel`.
- Example: Flajolet–Sedgewick's symbolic method ([Wikipedia: Symbolic method](https://en.wikipedia.org/wiki/Symbolic_method_%28combinatorics%29)).
- See also: T448, T449, T62, T79

### T448 Exponential formula
`compute` · stage: argue · signals: sequence, exact-value
aka: exp of connected structures, labelled structures, connected components, set partitions, labelled graphs, permutations by cycles
- What: the EGF of all structures is the exponential of the EGF of the connected ones.
- Fits when: labelled structures built as sets of connected components.
- Lean: coefficient identities in `PowerSeries`; small cases by `decide +kernel`.
- Example: [Wikipedia: Exponential formula](https://en.wikipedia.org/wiki/Exponential_formula).
- See also: T447, T461

### T449 Singularity analysis
`compute` `bound` · stage: argue · signals: sequence, asymptotic, analytic
aka: transfer theorems, dominant singularity, analytic combinatorics, Darboux's method, coefficient asymptotics, algebraic and meromorphic generating functions
- What: the location and type of the dominant singularity give coefficient asymptotics.
- Fits when: counting asymptotically with an algebraic or meromorphic generating function.
- Lean: —
- Example: transfer theorems of analytic combinatorics ([Wikipedia: Analytic combinatorics](https://en.wikipedia.org/wiki/Analytic_combinatorics)).
- See also: T447, T450, T705, T696

### T450 Analytic combinatorics in several variables
`compute` `bound` · stage: argue · signals: sequence, asymptotic, analytic
aka: ACSV, multivariate generating functions, singular variety, smooth points, bivariate counts, limit laws for statistics, Pemantle–Wilson
- What: asymptotics of multivariate coefficients from the geometry of the singular variety.
- Fits when: bivariate counts (statistics of objects) where univariate singularity analysis does not apply.
- Lean: —
- Example: Pemantle–Wilson, smooth points ([arXiv:math/0003192](https://arxiv.org/abs/math/0003192)).
- See also: T449, T705

### T451 Lagrange inversion
`compute` · stage: argue · signals: sequence, exact-value
aka: compositional inverse, T = xφ(T), Lagrange–Bürmann formula, tree enumeration, labelled trees, plane trees, Cayley's formula
- What: closed-form coefficients of the compositional inverse of a power series.
- Fits when: tree-like families defined by T = xφ(T).
- Lean: single coefficients by `decide +kernel`.
- Example: counting labelled and plane trees ([Wikipedia: Lagrange inversion theorem](https://en.wikipedia.org/wiki/Lagrange_inversion_theorem)).
- See also: T447, T461

### T452 Kernel method
`compute` · stage: argue · signals: sequence, exact-value
aka: catalytic variables, functional equations, quadratic method, lattice paths in the quarter plane, planar maps, permutation classes, algebraicity
- What: solves a functional equation with a catalytic variable by substituting roots of its kernel.
- Fits when: lattice paths, maps or permutation classes with a recursive decomposition.
- Lean: the final algebraic equation for the series checked with `ring` on `PowerSeries`; small coefficients by `decide +kernel`.
- Example: Bousquet-Mélou–Jehanne: such series are algebraic ([arXiv:math/0504018](https://arxiv.org/abs/math/0504018)).
- See also: T447, T62

### T453 Goulden–Jackson cluster method
`compute` · stage: argue · signals: sequence, exact-value, local-constraints
aka: cluster method, pattern avoidance in words, forbidden factors, overlapping bad words, Noonan–Zeilberger, avoiding consecutive patterns
- What: the generating function of words avoiding given factors, built from clusters of overlapping bad words.
- Fits when: pattern avoidance in words or sequences.
- Lean: the rational generating function's coefficients by `decide +kernel` against a brute-force count for small n.
- Example: Noonan–Zeilberger's extensions and Maple implementations ([arXiv:math/9806036](https://arxiv.org/abs/math/9806036)).
- See also: T338, T447, T21

### T454 Möbius inversion on posets
`prove` `compute` · stage: argue · signals: order, integers, exact-value
aka: incidence algebra, Rota, Möbius function μ, zeta transform, fast subset convolution, inclusion–exclusion over divisors, subsets, partitions, subspaces, "stop and use μ"
- What: inverts summation over a poset via its Möbius function.
- Fits when: inclusion–exclusion over divisors, subsets, partitions, subspaces; "stop and use μ" (MO).
- Lean: Mathlib `IncidenceAlgebra.mu`; for divisors `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`.
- Example: Rota's incidence-algebra framework, generalizing the number-theoretic Möbius function ([Wikipedia: Incidence algebra](https://en.wikipedia.org/wiki/Incidence_algebra), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T338, T455, T1114

### T455 Burnside and Pólya enumeration
`compute` · stage: argue · signals: group, symmetric, exact-value
aka: Burnside's lemma, Cauchy–Frobenius lemma, orbit counting, cycle index, Pólya enumeration theorem, counting by symmetry classes, necklaces, isomers, colourings up to symmetry
- What: counts orbits as the average number of fixed points; the cycle index handles colourings.
- Fits when: counting up to symmetry.
- Lean: Mathlib `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`; a specific count by `decide +kernel`.
- Example: necklaces and isomer counting ([Wikipedia: Burnside's lemma](https://en.wikipedia.org/wiki/Burnside's_lemma), [Wikipedia: Pólya enumeration theorem](https://en.wikipedia.org/wiki/Pólya_enumeration_theorem)).
- See also: T344, T38, T30

### T456 RSK correspondence
`prove` `compute` · stage: argue · signals: order, sequence, identity
aka: Robinson–Schensted–Knuth, Schensted insertion, Young tableaux, longest increasing subsequence, Cauchy identity, plane partitions
- What: bijects matrices or permutations with pairs of tableaux.
- Fits when: increasing subsequences, symmetric-function identities.
- Lean: Mathlib has `YoungDiagram`; a bijection on a finite range by `decide +kernel`.
- Example: Schensted: the first row of the tableau has the length of the longest increasing subsequence ([Wikipedia: RSK correspondence](https://en.wikipedia.org/wiki/Robinson–Schensted–Knuth_correspondence), [Wikipedia: Longest increasing subsequence](https://en.wikipedia.org/wiki/Longest_increasing_subsequence)).
- See also: T336, T457

### T457 Probabilistic proofs of exact formulas
`prove` · stage: argue · signals: random, exact-value, identity
aka: hook walk, random process telescoping, hook length formula, Greene–Nijenhuis–Wilf, product formulas without bijections
- What: designs a random process whose outcome probabilities telescope to the formula.
- Fits when: product formulas (hook lengths) without obvious bijections.
- Lean: the formula for small shapes by `decide +kernel`.
- Example: Greene–Nijenhuis–Wilf's hook walk proof of the hook length formula ([Wikipedia: Hook length formula](https://en.wikipedia.org/wiki/Hook_length_formula)).
- See also: T456, T336

### T458 q-series and partition bijections
`prove` · stage: argue · signals: sequence, identity, integers
aka: partition identities, Jacobi triple product, Rogers–Ramanujan identities, Euler's pentagonal number theorem, Glaisher bijection, odd and distinct parts, product sides
- What: proves partition identities by q-series manipulation (Jacobi triple product) or by bijection.
- Fits when: partition identities with product sides.
- Lean: Mathlib `Nat.Partition.genFun` (Partition/GenFun.lean); finitely many coefficients by `decide +kernel`.
- Example: the Rogers–Ramanujan identities ([Wikipedia: Rogers–Ramanujan identities](https://en.wikipedia.org/wiki/Rogers–Ramanujan_identities)).
- See also: T336, T556, T553

### T459 Laurent phenomenon
`prove` · stage: argue · signals: polynomial, sequence, integers
aka: cluster algebras, Fomin–Zelevinsky, Somos sequences, nonlinear recurrences with integer terms, cluster variables, mutation
- What: shows terms of a rational recurrence are Laurent polynomials in the initial values, hence integers.
- Fits when: integrality of nonlinear recurrences.
- Lean: terms of a given recurrence checked integral by `norm_num` for a finite range.
- Example: Fomin–Zelevinsky: cluster variables are Laurent polynomials in any cluster, explaining integrality of such recurrences ([Wikipedia: Cluster algebra](https://en.wikipedia.org/wiki/Cluster_algebra)).
- See also: T62

### T460 Combinatorial reciprocity
`prove` · stage: argue · signals: polynomial, geometry, identity
aka: Ehrhart–Macdonald reciprocity, Ehrhart polynomial, chromatic polynomial at negative integers, order polynomials, interior lattice points, Stanley reciprocity
- What: a counting polynomial evaluated at negative integers counts interior or complementary objects.
- Fits when: lattice-point or colouring polynomials.
- Lean: —
- Example: Ehrhart–Macdonald reciprocity, L(P,−t) = (−1)^d L(int P, t) ([Wikipedia: Ehrhart polynomial](https://en.wikipedia.org/wiki/Ehrhart_polynomial)).
- See also: T747, T474

### T461 Combinatorial species
`prove` `compute` · stage: argue · signals: sequence, identity, exact-value
aka: Joyal species, functorial combinatorics, labelled structures, bijective proofs, Cayley's formula, doubly rooted trees
- What: a functorial calculus of labelled structures; identities hold at the level of structures.
- Fits when: labelled enumeration with symmetries.
- Lean: the resulting counts by `decide +kernel` for small sizes.
- Example: Joyal's bijective proof of Cayley's formula via doubly rooted trees ([Wikipedia: Combinatorial species](https://en.wikipedia.org/wiki/Combinatorial_species), [Wikipedia: Cayley's formula](https://en.wikipedia.org/wiki/Cayley's_formula)).
- See also: T447, T448, T336

### T462 Stanley–Reisner rings
`prove` `bound` · stage: argue · signals: polynomial, topology, inequality
aka: face rings, commutative algebra for simplicial complexes, Cohen–Macaulay complexes, Hilbert series, f-vectors, h-vectors, upper bound theorem, simplicial spheres
- What: encodes a simplicial complex as a ring; Cohen–Macaulayness and the Hilbert series constrain f-vectors.
- Fits when: face-number inequalities of polytopes and spheres.
- Lean: —
- Example: Stanley's proof of the upper bound conjecture for simplicial spheres ([Wikipedia: Upper bound theorem](https://en.wikipedia.org/wiki/Upper_bound_theorem), [Wikipedia: Stanley–Reisner ring](https://en.wikipedia.org/wiki/Stanley–Reisner_ring)).
- See also: T463, T590

### T463 Combinatorial Lefschetz theorems
`prove` · stage: argue · signals: topology, polynomial, inequality
aka: hard Lefschetz without positivity, generic Artinian reduction, g-conjecture, Dehn–Sommerville, simplicial spheres, anisotropy
- What: proves hard Lefschetz for face rings via generic Artinian reductions, without positivity.
- Fits when: face-number conjectures beyond polytopes.
- Lean: —
- Example: Adiprasito's proof of the g-conjecture for simplicial spheres ([arXiv:1812.10454](https://arxiv.org/abs/1812.10454), [Wikipedia: Dehn–Sommerville equations](https://en.wikipedia.org/wiki/Dehn–Sommerville_equations)).
- See also: T462
