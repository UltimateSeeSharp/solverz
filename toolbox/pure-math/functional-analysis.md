# Functional analysis
Banach and Hilbert space principles, compactness, extreme points, spectral theory, fixed-point theorems, variational principles, amenability, exotic spaces, free probability.

### T652 Hahn–Banach separation and extension
`prove` · stage: argue · signals: operator, geometry
aka: Hahn–Banach theorem, separating hyperplanes, extension of functionals, Banach limits, invariant means, duality certificates, convex separation
- What: separate convex sets by functionals; extend bounded functionals.
- Fits when: duality arguments; existence of invariant means or certificates.
- Lean: Mathlib: `exists_extension_norm_eq`, `geometric_hahn_banach_open`.
- Example: Banach limits and separation theorems ([Wikipedia: Hahn–Banach theorem](https://en.wikipedia.org/wiki/Hahn–Banach_theorem)).
- See also: T316, T48, T664

### T653 Baire category
`prove` `find` · stage: argue · signals: operator, topology, construction
aka: Baire category theorem, generic elements, comeagre sets, nowhere dense, residual sets, nowhere differentiable functions, for-all/there-exists swap
- What: in a complete metric space a countable union of nowhere dense sets has empty interior, so typical elements exist.
- Fits when: proving existence of "generic" pathological objects without constructing them.
- Lean: Mathlib: `dense_iInter_of_isOpen`.
- Example: perfect sets are uncountable; Banach's category proof that most continuous functions are nowhere differentiable ([Wikipedia: Baire category theorem](https://en.wikipedia.org/wiki/Baire_category_theorem), [Tricki: for all/there exists swap](https://www.tricki.org/article/How_to_change_for_all_x_there_exists_y_into_there_exists_y_such_that_for_all_x)).
- See also: T654, T374

### T654 Uniform boundedness principle
`prove` `find` · stage: argue · signals: operator, construction
aka: Banach–Steinhaus theorem, pointwise bounded families, divergence somewhere, condensation of singularities, divergent Fourier series
- What: pointwise bounded families of operators are uniformly bounded; otherwise a single bad point exists.
- Fits when: showing divergence happens somewhere.
- Lean: Mathlib: `banach_steinhaus`.
- Example: a continuous function with divergent Fourier series ([Wikipedia: Uniform boundedness principle](https://en.wikipedia.org/wiki/Uniform_boundedness_principle)).
- See also: T653, T655

### T655 Open mapping and closed graph
`prove` · stage: argue · signals: operator
aka: open mapping theorem, closed graph theorem, bounded inverse theorem, automatic continuity, a priori estimates for free
- What: surjective bounded operators are open; closed graphs give boundedness for free.
- Fits when: automatic continuity and a priori estimates.
- Lean: Mathlib: `ContinuousLinearMap.isOpenMap`, `LinearMap.continuous_of_isClosed_graph`.
- Example: open mapping theorem ([Wikipedia: Open mapping theorem](https://en.wikipedia.org/wiki/Open_mapping_theorem_%28functional_analysis%29)).
- See also: T654, T321

### T656 Compactness in function spaces (Arzelà–Ascoli, Banach–Alaoglu)
`prove` `find` · stage: argue · signals: operator, analytic, topology
aka: Arzelà–Ascoli, Banach–Alaoglu, equicontinuity, weak-* compactness, convergent subsequences, existence by approximation and limit, Peano existence theorem
- What: equicontinuous or bounded families have convergent subsequences in a suitable topology.
- Fits when: existence by approximation and limit.
- Lean: Mathlib: `BoundedContinuousFunction.arzela_ascoli`, `WeakDual.isCompact_polar` (Banach–Alaoglu).
- Example: Peano's existence theorem for ODEs via Arzelà–Ascoli ([Wikipedia: Arzelà–Ascoli theorem](https://en.wikipedia.org/wiki/Arzelà–Ascoli_theorem), [Wikipedia: Banach–Alaoglu theorem](https://en.wikipedia.org/wiki/Banach–Alaoglu_theorem), [Tricki: How to use compactness](https://www.tricki.org/article/How_to_use_compactness)).
- See also: T318, T676, T679

### T657 Extreme points (Krein–Milman, Choquet)
`prove` · stage: argue · signals: operator, matrix, geometry
aka: Krein–Milman theorem, Choquet theory, extreme points, Birkhoff–von Neumann, doubly stochastic matrices, permutation matrices, linear functionals on convex sets
- What: linear functionals on compact convex sets are extremized at extreme points.
- Fits when: optimizing linear functionals over convex sets of matrices or measures.
- Lean: Mathlib: `closure_convexHull_extremePoints` (Krein–Milman), `doublyStochastic_eq_convexHull_permMatrix` (Birkhoff).
- Example: Birkhoff–von Neumann: doubly stochastic matrices are convex combinations of permutation matrices ([Wikipedia: Krein–Milman theorem](https://en.wikipedia.org/wiki/Krein–Milman_theorem), [Wikipedia: Doubly stochastic matrix](https://en.wikipedia.org/wiki/Doubly_stochastic_matrix)).
- See also: T608, T48

### T658 Spectral theorem and functional calculus
`prove` · stage: argue · signals: operator, matrix
aka: spectral theorem, diagonalization, self-adjoint operators, normal operators, functional calculus, graph Laplacians, quantum operators, eigenvector basis
- What: diagonalize normal operators and apply functions to them.
- Fits when: self-adjoint operators, quantum or graph Laplacians.
- Lean: Mathlib: `Matrix.IsHermitian.spectral_theorem`, `LinearMap.IsSymmetric.eigenvectorBasis`, continuous functional calculus `cfc`.
- Example: the spectral theorem ([Wikipedia: Spectral theorem](https://en.wikipedia.org/wiki/Spectral_theorem)).
- See also: T400, T411, T72

### T659 Fredholm alternative and index
`prove` · stage: argue · signals: operator, pde
aka: Fredholm alternative, Fredholm index, compact perturbations of the identity, integral equations, elliptic equations, Riesz–Schauder theory
- What: compact perturbations of the identity are invertible iff injective; the index is a deformation invariant.
- Fits when: solvability of integral and elliptic equations.
- Lean: Mathlib: `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` (`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`).
- Example: the Fredholm alternative for integral equations ([Wikipedia: Fredholm alternative](https://en.wikipedia.org/wiki/Fredholm_alternative)).
- See also: T693, T660

### T660 Lax–Milgram (coercive forms)
`prove` · stage: argue · signals: operator, pde
aka: Lax–Milgram theorem, coercive bilinear forms, weak solutions, Dirichlet problem, Riesz representation, variational formulation
- What: coercive bilinear forms give unique weak solutions.
- Fits when: existence for linear elliptic PDE.
- Lean: Mathlib: `IsCoercive.continuousLinearEquivOfBilin` (`Analysis/InnerProductSpace/LaxMilgram.lean`).
- Example: weak solutions of the Dirichlet problem ([Wikipedia: Lax–Milgram theorem](https://en.wikipedia.org/wiki/Lax–Milgram_theorem)).
- See also: T676, T675

### T661 Contraction mapping
`prove` `find` · stage: argue · signals: operator, analytic, dynamics, construction
aka: Banach fixed-point theorem, contraction principle, Picard iteration, Picard–Lindelöf, local existence for ODE and PDE, implicit function theorem, a posteriori error bounds
- What: a strict contraction on a complete space has a unique fixed point.
- Fits when: local existence for ODE and PDE; implicit function theorems.
- Lean: Mathlib: `ContractingWith.fixedPoint`, `IsPicardLindelof` (`Analysis/ODE/PicardLindelof.lean`).
- Example: Picard–Lindelöf via Banach's fixed point theorem ([Wikipedia: Banach fixed-point theorem](https://en.wikipedia.org/wiki/Banach_fixed-point_theorem)).
- See also: T68, T662, T831

### T662 Topological fixed points (Schauder, Leray–Schauder, Kakutani)
`prove` `find` · stage: argue · signals: operator, topology, game
aka: Schauder fixed-point theorem, Leray–Schauder degree, Kakutani fixed-point theorem, set-valued maps, Nash equilibria, nonlinear existence without uniqueness
- What: continuous self-maps of compact convex sets have fixed points; set-valued versions too.
- Fits when: nonlinear existence without uniqueness; equilibria.
- Lean: — (Schauder, Kakutani and Brouwer fixed-point theorems not found in Mathlib).
- Example: Nash equilibria via Kakutani's fixed point theorem ([Wikipedia: Kakutani fixed-point theorem](https://en.wikipedia.org/wiki/Kakutani_fixed-point_theorem), [Wikipedia: Schauder fixed-point theorem](https://en.wikipedia.org/wiki/Schauder_fixed-point_theorem), [Wikipedia: Leray–Schauder degree](https://en.wikipedia.org/wiki/Leray–Schauder_degree), [Tricki: fixed point theorems](https://www.tricki.org/article/How_to_use_fixed_point_theorems)).
- See also: T707, T661, T712

### T663 Order-theoretic fixed points (Knaster–Tarski)
`prove` `find` · stage: argue · signals: order, logic, construction
aka: Knaster–Tarski theorem, least fixed point, greatest fixed point, monotone maps on complete lattices, inductive definitions, Schröder–Bernstein, closure operators
- What: monotone maps on complete lattices have least and greatest fixed points.
- Fits when: constructions defined by monotone closure; bijections from two injections.
- Lean: Mathlib: `OrderHom.lfp`, `OrderHom.gfp`, `Function.Embedding.schroeder_bernstein`.
- Example: a proof of the Schröder–Bernstein theorem ([Wikipedia: Knaster–Tarski theorem](https://en.wikipedia.org/wiki/Knaster–Tarski_theorem)).
- See also: T767

### T664 Common fixed points of commuting maps (Markov–Kakutani)
`prove` · stage: argue · signals: group, operator
aka: Markov–Kakutani theorem, commuting affine maps, invariant means, invariant measures, amenable groups, abelian groups are amenable
- What: commuting affine maps have a common fixed point, giving invariant means.
- Fits when: amenability; invariant measures.
- Lean: — (Markov–Kakutani and amenable groups not found in Mathlib).
- Example: one of the quickest proofs that abelian groups are amenable ([Wikipedia: Markov–Kakutani fixed-point theorem](https://en.wikipedia.org/wiki/Markov–Kakutani_fixed-point_theorem), [Wikipedia: Amenable group](https://en.wikipedia.org/wiki/Amenable_group)).
- See also: T666, T652

### T665 Ekeland's variational principle
`prove` · stage: argue · signals: operator, analytic
aka: Ekeland's principle, approximate minimizers, tilted functional, Caristi fixed-point theorem, Palais–Smale sequences, minimization without compactness
- What: approximate minimizers can be perturbed into exact minimizers of a slightly tilted functional.
- Fits when: functionals without compactness.
- Lean: — (Ekeland and Caristi not found in Mathlib).
- Example: Caristi's fixed point theorem via Ekeland ([Wikipedia: Ekeland's variational principle](https://en.wikipedia.org/wiki/Ekeland's_variational_principle)).
- See also: T676, T677

### T666 Paradoxical decompositions and amenability
`prove` `find` · stage: argue · signals: group, geometry, construction
aka: Banach–Tarski paradox, Tarski's circle squaring, Laczkovich, equidecomposability, free subgroups, amenability, Borel circle squaring, Marks–Unger
- What: free subgroups enable paradoxical decompositions; amenability forbids them.
- Fits when: equidecomposability questions.
- Lean: — (Banach–Tarski not found in Mathlib).
- Example: Banach–Tarski paradox; Laczkovich's circle squaring; Marks–Unger's Borel circle squaring ([Wikipedia: Banach–Tarski paradox](https://en.wikipedia.org/wiki/Banach–Tarski_paradox), [Wikipedia: Tarski's circle-squaring problem](https://en.wikipedia.org/wiki/Tarski's_circle-squaring_problem), [arXiv:1612.05833](https://arxiv.org/abs/1612.05833)).
- See also: T574, T664, T772

### T667 Exotic constructions by inductive norms
`find` · stage: construct · signals: operator, construction
aka: Tsirelson space, implicit recursive norms, no copy of ℓ^p or c_0, Banach space counterexamples, Gowers–Maurey
- What: define a norm by an implicit recursive formula to kill all ℓ^p subspaces.
- Fits when: counterexamples in Banach space theory.
- Lean: — (Tsirelson's space not found in Mathlib).
- Example: Tsirelson's space with no copy of ℓ^p or c_0 ([Wikipedia: Tsirelson space](https://en.wikipedia.org/wiki/Tsirelson_space)).
- See also: T653

### T668 Stochastic localization
`prove` `bound` · stage: argue · signals: geometry, random, inequality
aka: Eldan's stochastic localization, martingale of tilts, KLS conjecture, Bourgain's slicing problem, log-concave measures, isoperimetry, thin shell
- What: evolve a measure by a martingale of tilts until it is nearly Gaussian; control the covariance along the way.
- Fits when: isoperimetry and concentration for log-concave measures.
- Lean: —
- Example: Chen's near-constant KLS bound; Klartag–Lehec's resolution of Bourgain's slicing problem ([arXiv:2011.13661](https://arxiv.org/abs/2011.13661), [arXiv:2412.15044](https://arxiv.org/abs/2412.15044)).
- See also: T778, T383, T611

### T669 Free probability
`bound` `prove` · stage: argue · signals: operator, matrix, random, inequality
aka: free independence, free convolution, finite free convolution, R-transform, spectra of sums of random matrices, characteristic polynomials, interlacing families
- What: noncommutative independence; free convolutions predict spectra of sums of large random matrices, and finite versions act on characteristic polynomials.
- Fits when: spectra of sums or products of matrices; interlacing-family arguments.
- Lean: — (free probability not found in Mathlib).
- Example: Marcus–Spielman–Srivastava's finite free convolutions ([arXiv:1504.00350](https://arxiv.org/abs/1504.00350), [Wikipedia: Free probability](https://en.wikipedia.org/wiki/Free_probability)).
- See also: T403, T400
