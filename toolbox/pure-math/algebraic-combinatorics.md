# Algebraic and spectral methods in combinatorics
Polynomials, linear algebra and eigenvalues as proof tools: Nullstellensatz, Chevalley–Warning, polynomial method, slice rank, partitioning, dimension arguments, interlacing, real-stable and Lorentzian polynomials, determinants.

### T391 Combinatorial Nullstellensatz
`prove` `find` · stage: argue · signals: polynomial, additive, colouring
aka: Alon's Nullstellensatz, nonvanishing coefficient, grid, Cauchy–Davenport, Erdős–Heilbronn conjecture, Alon–Füredi hyperplane covers, list colouring, sumset lower bounds
- What: a polynomial of degree Σt_i with nonzero coefficient of Πx_i^{t_i} does not vanish on a grid S_1×…×S_n with |S_i| > t_i.
- Fits when: sumset lower bounds, list colouring, covering problems over fields; the property becomes "some product of linear forms is nonzero".
- Lean: Mathlib: `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero` (`Combinatorics/Nullstellensatz.lean`); one coefficient of a concrete polynomial by `decide +kernel` or `norm_num`.
- Example: Cauchy–Davenport, the Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune), Alon–Füredi hyperplane covers of the cube ([Alon: Combinatorial Nullstellensatz](https://www.tau.ac.il/~nogaa/PDFS/null2.pdf)).
- See also: T392, T467, T423, T60

### T392 Chevalley–Warning and zero-sum theory
`prove` · stage: argue · signals: finite-field, additive, congruence
aka: Chevalley–Warning theorem, zero-sum problems, Erdős–Ginzburg–Ziv theorem, Davenport constant, solutions mod p
- What: low-degree polynomial systems over F_p have a number of zeros divisible by p.
- Fits when: existence of zero-sum subsequences or solutions mod p.
- Lean: Mathlib: `FiniteField.char_dvd_card_solutions` (`FieldTheory/ChevalleyWarning.lean`), `ZMod.erdos_ginzburg_ziv`, `Int.erdos_ginzburg_ziv`.
- Example: the Erdős–Ginzburg–Ziv theorem (2n - 1 integers contain n summing to 0 mod n) ([Wikipedia: Chevalley–Warning theorem](https://en.wikipedia.org/wiki/Chevalley–Warning_theorem), [Wikipedia: Erdős–Ginzburg–Ziv theorem](https://en.wikipedia.org/wiki/Erdős–Ginzburg–Ziv_theorem), [Alon: Combinatorial Nullstellensatz](https://www.tau.ac.il/~nogaa/PDFS/null2.pdf)).
- See also: T391, T332

### T393 Polynomial method
`prove` `bound` · stage: argue · signals: polynomial, finite-field, geometry
aka: vanishing of low-degree polynomials, Dvir's method, finite-field Kakeya, incidence problems, restriction to lines
- What: a set too small to escape a low-degree polynomial is forced to be large by restricting the polynomial to lines or curves.
- Fits when: incidence or Kakeya-type problems over finite fields.
- Lean: polynomial dimension counts and `Polynomial.card_roots'` in Mathlib; a grep finds no Kakeya theorem.
- Example: Dvir's Kakeya theorem over F_q ([arXiv:0803.2336](https://arxiv.org/abs/0803.2336), [Wikipedia: Polynomial method in combinatorics](https://en.wikipedia.org/wiki/Polynomial_method_in_combinatorics)).
- See also: T305, T394, T396, T309

### T394 Method of multiplicities
`bound` · stage: argue · signals: polynomial, finite-field, geometry
aka: vanishing to high order, Hasse derivatives, Kakeya sets in F_q^n, sharp constants
- What: require the auxiliary polynomial to vanish to high order, multiplying the leverage.
- Fits when: plain vanishing loses constant factors.
- Lean: —
- Example: Kakeya sets in F_q^n have size ≥ q^n/2^n, tight up to a 2 + o(1) factor ([arXiv:0901.2529](https://arxiv.org/abs/0901.2529)).
- See also: T393

### T395 Slice rank
`bound` · stage: argue · signals: finite-field, additive, product-structure
aka: Croot–Lev–Pach method, Ellenberg–Gijswijt bound, cap set problem, tensor rank, 3-AP-free sets in F_3^n, polynomial method for progressions
- What: write the indicator of the forbidden pattern as a low-rank tensor; the diagonal of a set without the pattern has full rank.
- Fits when: sets in F_p^n avoiding a linear pattern.
- Lean: the cap set bound was formalized in Lean 3 (Dahmen–Hölzl–Lewis 2019, [Wikipedia: Cap set](https://en.wikipedia.org/wiki/Cap_set)); a grep finds no cap set theorem in Mathlib.
- Example: the cap set problem: 3-AP-free sets in F_3^n are exponentially smaller than 3^n ([arXiv:1605.01506](https://arxiv.org/abs/1605.01506), [arXiv:1605.09223](https://arxiv.org/abs/1605.09223), [Tao: symmetric capset bound](https://terrytao.wordpress.com/2016/05/18/a-symmetric-formulation-of-the-croot-lev-pach-ellenberg-gijswijt-capset-bound/)).
- See also: T393, T309, T412

### T396 Polynomial partitioning
`bound` · stage: argue · signals: polynomial, geometry
aka: Guth–Katz partitioning, cell decomposition by a polynomial, distinct distances problem, incidence bounds in R^n, Fourier restriction, wave packets
- What: a polynomial of degree D cuts space into ~D^n cells with equal shares of the points; recurse and treat the zero set separately.
- Fits when: incidence problems in R^n where cell decompositions are too weak; Fourier restriction estimates in R^3 and up (wave packets organized by the partitioning polynomial).
- Lean: —
- Example: Guth–Katz near-resolution of Erdős's distinct distances problem ([arXiv:1011.4105](https://arxiv.org/abs/1011.4105)); Guth's restriction estimate ([arXiv:1407.1916](https://arxiv.org/abs/1407.1916)).
- See also: T397, T739, T738

### T397 Joints and ruled-surface arguments
`bound` · stage: argue · signals: polynomial, geometry
aka: joints problem, lines in R^3, Bezout counting, ruled surfaces, Guth–Katz
- What: low-degree polynomials vanishing on lines must vanish on many of them; Bezout counts intersections.
- Fits when: line configurations in R^3 or F^3.
- Lean: —
- Example: Guth–Katz solution of the joints problem ([arXiv:0812.1043](https://arxiv.org/abs/0812.1043)).
- See also: T396, T393

### T398 Dimension arguments
`bound` `prove` · stage: argue · signals: set-family, matrix, inequality
aka: linear algebra method, characteristic vectors, polynomial spaces, Oddtown, Eventown, Fisher's inequality, Frankl–Pach proof of Sauer–Shelah, rank bounds
- What: map the objects to vectors (characteristic vectors, polynomials) that are independent; their count is ≤ the dimension.
- Fits when: the maximum is far from unique and the constraints are about intersections mod p.
- Lean: Mathlib: `LinearIndependent` with `LinearIndependent.fintype_card_le_finrank`; small cases by `decide +kernel`.
- Example: Oddtown (odd sets with even pairwise intersections number ≤ n); the Frankl–Pach linear-algebra proof of Sauer–Shelah ([Tricki: Dimension arguments in combinatorics](https://www.tricki.org/article/Dimension_arguments_in_combinatorics)); Fisher's inequality ([Wikipedia: Fisher's inequality](https://en.wikipedia.org/wiki/Fisher%27s_inequality)).
- See also: T399, T371, T741

### T399 Frankl–Wilson modular intersection theorems
`bound` `find` · stage: argue · signals: set-family, geometry, congruence
aka: Ray-Chaudhuri–Wilson, restricted intersections mod p, chromatic number of R^n, Hadwiger–Nelson problem, Borsuk's conjecture counterexample, Kahn–Kalai
- What: restricted intersections mod p bound a family by a binomial coefficient via polynomial spaces.
- Fits when: geometric colouring and diameter problems in high dimension.
- Lean: —
- Example: exponential lower bounds for the chromatic number of R^n; the Kahn–Kalai Borsuk counterexample ([Wikipedia: Hadwiger–Nelson problem](https://en.wikipedia.org/wiki/Hadwiger–Nelson_problem), [Wikipedia: Borsuk's conjecture](https://en.wikipedia.org/wiki/Borsuk's_conjecture)).
- See also: T398, T741

### T400 Eigenvalue interlacing
`prove` `bound` · stage: argue · signals: graph, matrix, inequality
aka: Cauchy interlacing, Cauchy interlacing on principal submatrices, Courant–Fischer min-max, sensitivity conjecture, Huang's theorem, induced subgraphs of the hypercube, signed adjacency matrix
- What: eigenvalues of principal submatrices interlace with those of the matrix, bounding induced substructures.
- Fits when: induced subgraphs, independence numbers, sensitivity.
- Lean: Huang's theorem is in Mathlib's Archive (`huang_degree_theorem` in `Archive/Sensitivity.lean`); Mathlib: `SimpleGraph.adjMatrix`, `Matrix.IsHermitian.eigenvalues`.
- Example: Huang's sensitivity theorem: every induced subgraph on 2^{n-1}+1 cube vertices has max degree ≥ √n ([arXiv:1907.00847](https://arxiv.org/abs/1907.00847), [Wikipedia: Min-max theorem](https://en.wikipedia.org/wiki/Min-max_theorem)).
- See also: T402, T403, T304

### T401 Integrality of eigenvalue multiplicities
`prove` · stage: argue · signals: graph, matrix, classification, impossibility
aka: strongly regular graphs, Moore graphs, Hoffman–Singleton theorem, degree 57, friendship theorem, feasibility conditions, eigenvalue multiplicities must be integers
- What: a strongly regular structure forces eigenvalues whose multiplicities must be integers, which only few parameters allow.
- Fits when: classifying highly regular graphs or designs.
- Lean: the friendship theorem is in Mathlib's Archive (`friendship_theorem`); Mathlib: `SimpleGraph.IsSRGWith`; the parameter arithmetic by `norm_num` or `decide +kernel`.
- Example: Hoffman–Singleton: a Moore graph of diameter 2 must have degree 2, 3, 7 or 57 (graphs exist for 2, 3 and 7; degree 57 is open); the friendship theorem ([Wikipedia: Moore graph](https://en.wikipedia.org/wiki/Moore_graph), [Wikipedia: Friendship graph](https://en.wikipedia.org/wiki/Friendship_graph)).
- See also: T400, T438

### T402 Expander mixing lemma and spectral bounds
`bound` `prove` · stage: argue · signals: graph, matrix, pseudorandom
aka: expander mixing lemma, second eigenvalue, spectral gap, Cheeger inequality, Hoffman ratio bound, Hoory–Linial–Wigderson survey, d-regular expanders, edge distribution, independence number
- What: the second eigenvalue controls edge distribution between any two vertex sets.
- Fits when: pseudorandom graphs, independence number bounds (Hoffman ratio bound).
- Lean: Mathlib: `SimpleGraph.adjMatrix`, `SimpleGraph.lapMatrix`; eigenvalue bounds of explicit matrices need exact certificates.
- Example: edge counts between sets in d-regular expanders ([Wikipedia: Expander mixing lemma](https://en.wikipedia.org/wiki/Expander_mixing_lemma)); Hoffman's ratio bound, whose certificate is an eigenvalue ([Haemers survey](https://arxiv.org/abs/2102.05529)).
- See also: T368, T400, T579, T1071

### T403 Interlacing families of polynomials
`find` `prove` · stage: argue · signals: matrix, polynomial, graph
aka: method of interlacing families, Marcus–Spielman–Srivastava, MSS I and II, real-rooted polynomials, mixed characteristic polynomials, zeros of partition functions, Lee–Yang theorem, Kadison–Singer problem, bipartite Ramanujan graphs, signings
- What: if a family's characteristic polynomials have a common interlacer, some member has roots below the expected polynomial's.
- Fits when: existence of a good member of a finite family of matrices (signings, partitions); a combinatorial quantity is encoded as a polynomial whose roots avoid a region.
- Lean: —
- Example: Marcus–Spielman–Srivastava: Kadison–Singer and bipartite Ramanujan graphs of every degree ([arXiv:1306.3969](https://arxiv.org/abs/1306.3969), [Wikipedia: Ramanujan graph](https://en.wikipedia.org/wiki/Ramanujan_graph)); Lee–Yang 1952 ([Wikipedia: Lee–Yang theorem](https://en.wikipedia.org/wiki/Lee%E2%80%93Yang_theorem)).
- See also: T404, T400, T801

### T404 Stable and hyperbolic polynomials
`bound` · stage: argue · signals: polynomial, matrix, inequality
aka: real stability, hyperbolic polynomials, capacity, Gurvits, permanents, van der Waerden permanent conjecture, mixed discriminants, matching counts
- What: real-stability is preserved by differentiation and specialization; capacity bounds coefficients.
- Fits when: permanent, mixed-discriminant and matching-count lower bounds.
- Lean: Mathlib defines `Matrix.permanent` (`LinearAlgebra/Matrix/Permanent.lean`).
- Example: van der Waerden's permanent conjecture: Egorychev via Alexandrov–Fenchel, Gurvits via capacity of stable polynomials ([Wikipedia: Permanent](https://en.wikipedia.org/wiki/Permanent_%28mathematics%29), [arXiv:0711.3496](https://arxiv.org/abs/0711.3496)).
- See also: T403, T405, T746

### T405 Lorentzian polynomials
`prove` · stage: argue · signals: polynomial, sequence, inequality
aka: Brändén–Huh, ultra-log-concavity, log-concavity, Mason's conjecture, matroid independent sets, completely log-concave polynomials
- What: a polynomial class with a Hodge–Riemann-type Hessian condition, closed under many operations; implies ultra-log-concavity.
- Fits when: log-concavity of matroid or convex-body sequences.
- Lean: —
- Example: Brändén–Huh's proof of the strongest Mason conjecture on independent sets of matroids ([arXiv:1902.03719](https://arxiv.org/abs/1902.03719)).
- See also: T404, T406

### T406 Combinatorial Hodge theory
`prove` · stage: argue · signals: polynomial, sequence, inequality
aka: hard Lefschetz, Hodge–Riemann relations, Chow rings of matroids, Heron–Rota–Welsh conjecture, Read's conjecture, chromatic polynomials, unimodality, log-concavity
- What: build a ring satisfying hard Lefschetz and Hodge–Riemann relations from combinatorial data; log-concavity follows.
- Fits when: unimodality or log-concavity conjectures for matroids, polytopes, posets.
- Lean: —
- Example: Adiprasito–Huh–Katz proof of the Heron–Rota–Welsh conjecture; Huh's proof of Read's conjecture on chromatic polynomials ([arXiv:1511.02888](https://arxiv.org/abs/1511.02888), [arXiv:1008.4749](https://arxiv.org/abs/1008.4749)).
- See also: T405, T463

### T407 Quasirandom groups
`prove` `bound` · stage: argue · signals: group, pseudorandom, additive
aka: Gowers' quasirandom groups, minimal representation dimension, product-free sets, Babai–Sós question, PSL_2(q), nonabelian additive combinatorics
- What: groups without small nontrivial representations mix fast; products of dense sets cover the group.
- Fits when: product-free sets, nonabelian additive combinatorics.
- Lean: —
- Example: Gowers' negative answer to Babai–Sós: PSL_2(q) has no product-free subset of positive density ([arXiv:0710.3877](https://arxiv.org/abs/0710.3877)).
- See also: T425, T565

### T408 Determinantal counting
`compute` `prove` · stage: argue · signals: matrix, exact-value, graph
aka: Lindström–Gessel–Viennot lemma, Kasteleyn's method, FKT algorithm, Pfaffian counting, Pfaffians, matrix-tree theorem, Kirchhoff's theorem, non-intersecting lattice paths, plane partitions, domino tilings, spanning trees, perfect matchings of planar graphs
- What: express a count as a determinant or Pfaffian, then evaluate algebraically.
- Fits when: non-intersecting paths, perfect matchings of planar graphs, spanning trees.
- Lean: Mathlib: `Matrix.det`, `SimpleGraph.lapMatrix`; a concrete determinant by `decide +kernel` or `norm_num [Matrix.det_succ_row_zero]`.
- Example: Lindström–Gessel–Viennot for plane partitions; Kasteleyn's domino-tiling count; Kirchhoff's matrix-tree theorem ([Wikipedia: LGV lemma](https://en.wikipedia.org/wiki/Lindström–Gessel–Viennot_lemma), [Wikipedia: FKT algorithm](https://en.wikipedia.org/wiki/FKT_algorithm), [Wikipedia: Kirchhoff's theorem](https://en.wikipedia.org/wiki/Kirchhoff's_theorem)).
- See also: T409, T804, T802

### T409 Sylvester's determinant identity
`compute` `prove` · stage: argue · signals: matrix, identity
aka: Weinstein–Aronszajn identity, det(I + AB) = det(I + BA), low-rank perturbations, Fredholm determinants, random matrices
- What: det(I + AB) = det(I + BA) swaps a large determinant for a small one.
- Fits when: low-rank perturbations, Fredholm determinants, random matrix computations.
- Lean: Mathlib: `Matrix.det_one_add_mul_comm` (`LinearAlgebra/Matrix/SchurComplement.lean`).
- Example: called "the most important identity in mathematics" by Deift, per Tao's MO comment ([Wikipedia: Weinstein–Aronszajn identity](https://en.wikipedia.org/wiki/Weinstein–Aronszajn_identity), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T408

### T410 Smith normal form invariants
`prove` `compute` · stage: argue · signals: matrix, integers, impossibility
aka: invariant factors, elementary divisors, integer matrices, sandpile groups, critical groups, codes over Z, finitely generated abelian groups
- What: reduce an integer matrix to diagonal form; invariant factors give group structure and integrality obstructions.
- Fits when: integer-matrix existence questions (sandpile groups, designs, codes over Z).
- Lean: Mathlib: `Submodule.smithNormalForm` (`LinearAlgebra/FreeModule/PID.lean`); a concrete form is checked as U·A·V = D with unimodular U, V by `decide +kernel`.
- Example: invariant factors give the structure theorem for finitely generated abelian groups ([Wikipedia: Smith normal form](https://en.wikipedia.org/wiki/Smith_normal_form)).
- See also: T439, T45

### T411 Perron–Frobenius
`compute` `bound` · stage: argue · signals: matrix, asymptotic, sequence
aka: Perron–Frobenius theorem, nonnegative matrices, irreducible matrices, spectral radius, transfer matrices, growth rates, stationary distributions, entropy of shifts
- What: a nonnegative irreducible matrix has a unique positive top eigenvector.
- Fits when: growth rates, Markov chains, counting walks, entropy of shifts.
- Lean: —
- Example: growth rates of transfer-matrix counts and stationary distributions ([Wikipedia: Perron–Frobenius theorem](https://en.wikipedia.org/wiki/Perron–Frobenius_theorem)).
- See also: T829, T833
