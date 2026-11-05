# Real and harmonic analysis
Fourier methods, decompositions and maximal functions, oscillatory integrals, restriction and Kakeya, dimension theory, approximation and limits of sequences.

### T627 Fourier transform for convolution problems
`prove` `bound` · stage: argue · signals: analytic, additive, finite-field
aka: Fourier analysis on Z/N and F_p^n, Plancherel, Parseval, counting linear configurations, 3-term progressions, Roth's theorem, convolution identities, discrete Fourier transform
- What: counts of linear configurations become sums of products of Fourier coefficients.
- Fits when: the problem is expressible through convolutions and inner products.
- Lean: Mathlib: `ZMod.dft` (`Analysis/Fourier/ZMod.lean`), Plancherel for L² (`Analysis/Fourier/LpSpace.lean`); finite sums over `ZMod n` by `decide +kernel` for small n.
- Example: Roth's theorem ([Tricki: convolutions and Fourier](https://www.tricki.org/article/If_your_problem_can_be_expressed_in_terms_of_convolutions_and_inner_products_then_take_the_Fourier_transform)).
- See also: T412, T414, T628

### T628 Poisson summation
`prove` `bound` · stage: argue · signals: analytic, geometry, identity
aka: Poisson summation formula, dual lattice, theta functions, functional equation, lattice point counts, Cohn–Elkies LP bound, sphere packing
- What: a lattice sum of f equals a dual-lattice sum of its Fourier transform.
- Fits when: theta functions, lattice point counts, LP bounds for packings.
- Lean: Mathlib: `Real.tsum_eq_tsum_fourier` and its decay variants (`Analysis/Fourier/PoissonSummation.lean`).
- Example: the functional equation of theta functions; Cohn–Elkies bounds ([Wikipedia: Poisson summation formula](https://en.wikipedia.org/wiki/Poisson_summation_formula), [arXiv:math/0110009](https://arxiv.org/abs/math/0110009)).
- See also: T50, T630, T644

### T629 Uncertainty principle
`prove` `bound` · stage: argue · signals: analytic, inequality, impossibility
aka: Heisenberg uncertainty, Hardy uncertainty principle, sign uncertainty, support size lower bounds, Donoho–Stark, localization in time and frequency
- What: a function and its Fourier transform cannot both be concentrated.
- Fits when: lower bounds on support sizes, sign uncertainty, localization.
- Lean: — (no uncertainty principle found in Mathlib).
- Example: Heisenberg and Hardy uncertainty principles ([Wikipedia: Uncertainty principle](https://en.wikipedia.org/wiki/Uncertainty_principle)).
- See also: T644, T628

### T630 Positive-definite functions (Bochner)
`bound` `prove` · stage: argue · signals: analytic, geometry, set-family, inequality
aka: Bochner's theorem, positive-definite kernels, nonnegative Fourier transform, Delsarte-type bounds, distance problems, LP and SDP bounds for codes and packings
- What: positive definiteness is equivalent to a nonnegative Fourier transform.
- Fits when: LP or SDP bounds for codes and packings; distance problems.
- Lean: — (Bochner's theorem not found in Mathlib); a specific auxiliary function's sign conditions are checked by hand or by T66.
- Example: Bochner's theorem; Delsarte-type bounds ([Wikipedia: Bochner's theorem](https://en.wikipedia.org/wiki/Bochner's_theorem)).
- See also: T50, T53, T628

### T631 Approximate identities and mollification
`prove` · stage: argue · signals: analytic
aka: mollifiers, bump functions, approximate delta, Fejér kernel, Fejér's theorem, Cesàro summability, smoothing by convolution
- What: convolve with a bump to smooth while barely changing the function.
- Fits when: approximating by smooth functions; summability of Fourier series.
- Lean: Mathlib: `ContDiffBump`, `MeasureTheory.convolution`, `ContDiffBump.convolution_tendsto_right_of_continuous`; the Fejér kernel not found.
- Example: Fejér's theorem via the Fejér kernel ([Wikipedia: Fejér kernel](https://en.wikipedia.org/wiki/Fejér_kernel), [Tricki: convolve with an approximate delta](https://www.tricki.org/article/To_make_a_function_nicer_without_changing_it_much_convolve_it_with_an_approximate_delta_function)).
- See also: T623, T645

### T632 Littlewood–Paley decomposition
`bound` · stage: argue · signals: analytic, pde, inequality
aka: dyadic frequency decomposition, square functions, Fourier multipliers, Besov spaces, paraproducts, nonlinear PDE estimates
- What: split a function into dyadic frequency pieces; square functions measure L^p norms.
- Fits when: multiplier bounds, nonlinear PDE estimates.
- Lean: — (not found in Mathlib).
- Example: Littlewood–Paley theory ([Wikipedia: Littlewood–Paley theory](https://en.wikipedia.org/wiki/Littlewood–Paley_theory)).
- See also: T620, T633, T639

### T633 Calderón–Zygmund decomposition
`bound` · stage: argue · signals: analytic, inequality
aka: Calderón–Zygmund lemma, good and bad parts, singular integrals, weak-type (1,1), stopping-time cubes, dyadic cubes
- What: split f into a good bounded part and bad parts with mean zero on disjoint cubes.
- Fits when: weak-type (1,1) bounds for singular integrals.
- Lean: — (not found in Mathlib).
- Example: the Calderón–Zygmund lemma ([Wikipedia: Calderón–Zygmund lemma](https://en.wikipedia.org/wiki/Calderón–Zygmund_lemma)).
- See also: T634, T651, T632

### T634 Maximal functions and covering lemmas
`bound` `prove` · stage: argue · signals: analytic, geometry, inequality
aka: Hardy–Littlewood maximal function, Vitali covering lemma, Besicovitch covering, Lebesgue differentiation theorem, almost-everywhere convergence, maximal inequality
- What: control a supremum of averages via a Vitali covering argument.
- Fits when: almost-everywhere convergence, differentiation theorems.
- Lean: Mathlib: `Vitali.exists_disjoint_covering_ae`, `VitaliFamily.ae_tendsto_average` (Lebesgue differentiation).
- Example: Lebesgue differentiation via the Hardy–Littlewood maximal inequality ([Wikipedia: Hardy–Littlewood maximal function](https://en.wikipedia.org/wiki/Hardy–Littlewood_maximal_function), [Wikipedia: Vitali covering lemma](https://en.wikipedia.org/wiki/Vitali_covering_lemma)).
- See also: T633, T642

### T635 Interpolation (Riesz–Thorin, Marcinkiewicz)
`bound` · stage: argue · signals: analytic, operator, inequality
aka: Riesz–Thorin theorem, Marcinkiewicz interpolation, complex interpolation, real interpolation, Hausdorff–Young, weak-type bounds, operator bounds on L^p scales
- What: bounds at endpoints imply bounds in between.
- Fits when: operator bounds on a scale of spaces.
- Lean: — (Riesz–Thorin and Marcinkiewicz not found in Mathlib; three lines is T698).
- Example: Hausdorff–Young from Plancherel and the trivial L¹ bound ([Wikipedia: Riesz–Thorin theorem](https://en.wikipedia.org/wiki/Riesz–Thorin_theorem)).
- See also: T698, T607

### T636 Stationary phase and oscillatory integrals
`bound` `compute` · stage: argue · signals: analytic, asymptotic
aka: stationary phase, non-stationary phase, integration by parts for cancellation, van der Corput lemma, Fourier decay of surface measures, Bessel function asymptotics
- What: oscillatory integrals concentrate at critical points of the phase; elsewhere integrate by parts.
- Fits when: asymptotics of Fourier transforms of surface measures, Bessel functions.
- Lean: — (not found in Mathlib).
- Example: decay of Fourier transforms of curved surfaces ([Wikipedia: Stationary phase approximation](https://en.wikipedia.org/wiki/Stationary_phase_approximation), [Tricki: integration by parts for cancellation](https://www.tricki.org/article/Use_integration_by_parts_to_exploit_cancellation), [Tricki: method of stationary phase](https://www.tricki.org/article/method_of_stationary_phase)).
- See also: T705, T482, T637

### T637 TT* argument
`bound` · stage: argue · signals: analytic, operator, pde, inequality
aka: TT*, T*T, ‖T‖² = ‖TT*‖, Fourier extension, dispersive estimates, Strichartz estimates, Tomas–Stein
- What: bound T by bounding TT*, which is often an explicit convolution.
- Fits when: Fourier extension and dispersive estimates.
- Lean: Mathlib: the C*-identity `CStarRing.norm_star_mul_self`; Strichartz estimates not found.
- Example: Strichartz estimates ([Wikipedia: Strichartz estimate](https://en.wikipedia.org/wiki/Strichartz_estimate)).
- See also: T638, T636

### T638 Almost orthogonality (Cotlar–Stein, Schur test)
`bound` · stage: argue · signals: analytic, operator, inequality
aka: Cotlar–Stein lemma, Schur test, nearly orthogonal operators, row and column sums, Calderón–Vaillancourt, pseudodifferential operators
- What: a sum of nearly orthogonal operators is bounded; kernels with bounded row and column sums act boundedly.
- Fits when: operators decomposed into many pieces.
- Lean: — (Cotlar–Stein and the Schur test not found in Mathlib); a finite-matrix Schur test is elementary.
- Example: Calderón–Vaillancourt-type bounds via Cotlar–Stein ([Wikipedia: Cotlar–Stein lemma](https://en.wikipedia.org/wiki/Cotlar–Stein_lemma), [Wikipedia: Schur test](https://en.wikipedia.org/wiki/Schur_test)).
- See also: T637, T632

### T639 Decoupling
`bound` · stage: argue · signals: analytic, integers, inequality
aka: l² decoupling, Bourgain–Demeter–Guth, curved frequency supports, Vinogradov mean value theorem, exponential sums with curved phases, restriction, Strichartz
- What: L^p norms of sums of pieces with curved frequency supports are controlled by square sums of their norms.
- Fits when: exponential sums with curved phases; restriction; PDE.
- Lean: —
- Example: Bourgain–Demeter–Guth: Vinogradov's mean value theorem ([arXiv:1512.01565](https://arxiv.org/abs/1512.01565)).
- See also: T484, T632, T396

### T640 Multiscale induction for Kakeya-type sets
`prove` `bound` · stage: argue · signals: geometry, analytic, inequality
aka: induction on scales, sticky and grainy dichotomy, Kakeya conjecture, Furstenberg sets, projection problems, convex-set volume estimates, Wang–Zahl
- What: induct on scales with sticky/grainy structure dichotomies and convex-set volume estimates.
- Fits when: Kakeya, Furstenberg sets, projection problems.
- Lean: — (Kakeya not found in Mathlib).
- Example: Wang–Zahl's proof of the Kakeya conjecture in R^3; Ren–Wang's Furstenberg set estimate ([arXiv:2502.17655](https://arxiv.org/abs/2502.17655), [arXiv:2308.08819](https://arxiv.org/abs/2308.08819), [Wikipedia: Kakeya set](https://en.wikipedia.org/wiki/Kakeya_set)).
- See also: T396, T641, T750

### T641 Frostman measures and energy (dimension theory)
`prove` `bound` · stage: argue · signals: geometry, analytic, inequality
aka: Frostman's lemma, s-energy, capacity, Hausdorff dimension lower bounds, Falconer distance problem, projection theorems, Marstrand
- What: Hausdorff dimension ≥ s iff the set supports a measure with finite s-energy.
- Fits when: lower bounds on dimensions of sets; distance and projection problems.
- Lean: Mathlib defines `dimH` (`Topology/MetricSpace/HausdorffDimension.lean`); Frostman's lemma not found.
- Example: Frostman's lemma (dimension via s-capacity), the standard entry to Falconer's distance problem ([Wikipedia: Frostman lemma](https://en.wikipedia.org/wiki/Frostman_lemma), [Wikipedia: Falconer's conjecture](https://en.wikipedia.org/wiki/Falconer's_conjecture)).
- See also: T640, T750

### T642 Time–frequency analysis
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: phase-space tiles, wave packets, trees of tiles, Carleson's theorem, Lacey–Thiele, bilinear Hilbert transform, modulation-invariant maximal operators
- What: decompose into tiles in phase space and organize them by trees.
- Fits when: maximal operators involving modulations.
- Lean: — (Carleson's theorem not found in Mathlib).
- Example: Carleson's theorem on a.e. convergence of Fourier series ([Wikipedia: Carleson's theorem](https://en.wikipedia.org/wiki/Carleson's_theorem)).
- See also: T634, T632

### T643 Wiener-type Tauberian theorems
`prove` · stage: argue · signals: analytic, integers, asymptotic
aka: Wiener's Tauberian theorem, Wiener–Ikehara, closed span of translates, nonvanishing Fourier transform, Banach algebra L¹, prime number theorem
- What: translates of f ∈ L¹ span a dense subspace of L¹ iff f̂ has no real zeros.
- Fits when: Tauberian deductions (the prime number theorem is a standard application).
- Lean: — (Wiener's theorem not found in Mathlib; `NumberTheory/LSeries/PrimesInAP.lean` names Wiener–Ikehara only for an auxiliary function).
- Example: Wiener's Tauberian theorem ([Wikipedia: Wiener's Tauberian theorem](https://en.wikipedia.org/wiki/Wiener's_Tauberian_theorem)).
- See also: T478, T477

### T644 Paley–Wiener
`prove` `bound` · stage: argue · signals: analytic
aka: Paley–Wiener theorem, band-limited functions, entire functions of exponential type, compact Fourier support, auxiliary functions in LP bounds, Beurling–Selberg
- What: compact Fourier support corresponds to entire functions of exponential type.
- Fits when: band-limited extremal problems; auxiliary functions in LP bounds.
- Lean: — (not found in Mathlib).
- Example: Paley–Wiener theorem ([Wikipedia: Paley–Wiener theorem](https://en.wikipedia.org/wiki/Paley–Wiener_theorem)).
- See also: T501, T706, T50

### T645 Density + closure
`prove` · stage: argue · signals: analytic, topology
aka: prove on a dense subset, closedness of the good set, approximation theorems, Stone–Weierstrass, Weierstrass approximation, extension by continuity
- What: prove on a dense class, then show the set where it holds is closed.
- Fits when: approximation theorems; continuity of operators.
- Lean: Mathlib: `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` (Stone–Weierstrass), `polynomialFunctions_closure_eq_top`.
- Example: Lebesgue's proof of the Weierstrass approximation theorem ([Tricki: dense subset then closure](https://www.tricki.org/article/Prove_the_result_on_a_dense_subset_and_then_prove_that_the_set_where_the_result_holds_is_closed), [Wikipedia: Stone–Weierstrass theorem](https://en.wikipedia.org/wiki/Stone–Weierstrass_theorem)).
- See also: T623, T649, T321

### T646 Self-similarity for limits (subadditivity, Fekete)
`prove` `bound` · stage: argue · signals: sequence, asymptotic, product-structure
aka: Fekete's lemma, subadditive sequences, submultiplicative sequences, growth constants, Shannon capacity, connective constants, Ramsey limits, liminf equals limsup
- What: a subadditive, superadditive or self-similar sequence has a limit equal to its inf or sup.
- Fits when: growth constants (Shannon capacity, connective constants, Ramsey limits).
- Lean: Mathlib: `Subadditive.tendsto_lim`, `Submultiplicative.tendsto_lim` (`Analysis/Subadditive.lean`).
- Example: limits from liminf or limsup via self-similarity ([Tricki: self-similarity limits](https://www.tricki.org/article/Use_self-similarity_to_get_a_limit_from_an_inferior_or_superior_limit)).
- See also: T622, T607

### T647 Averaging out boundary terms
`bound` · stage: argue · signals: analytic, inequality
aka: average over the cutoff, random cutoff, kill boundary terms, summation by parts endpoints, truncation parameter averaging
- What: average over a cutoff parameter to kill the boundary terms of integration by parts.
- Fits when: summation by parts or truncations create bad endpoint terms.
- Lean: a hand proof; no special support.
- Example: the non-endpoint Sobolev inequality in the Tricki ([Tricki: average over a parameter](https://www.tricki.org/article/If_a_parameter_is_generating_undesirable_boundary_terms_try_averaging_over_many_choices_of_that_parameter)).
- See also: T648, T326

### T648 Euler–Maclaurin and summation by parts
`compute` `bound` · stage: argue · signals: analytic, sequence, asymptotic
aka: Euler–Maclaurin formula, Abel summation, summation by parts, sums to integrals, Bernoulli numbers, Stirling's formula, zeta asymptotics
- What: convert sums to integrals plus explicit corrections.
- Fits when: asymptotics of sums of smooth functions.
- Lean: Mathlib: `Finset.sum_range_by_parts`, `Stirling.stirlingSeq`; Euler–Maclaurin not found.
- Example: Stirling's formula and ζ asymptotics ([Wikipedia: Euler–Maclaurin formula](https://en.wikipedia.org/wiki/Euler–Maclaurin_formula), [Wikipedia: Summation by parts](https://en.wikipedia.org/wiki/Summation_by_parts)).
- See also: T500, T705, T71

### T649 Constructive approximation (Bernstein polynomials)
`find` · stage: construct · signals: polynomial, analytic, construction
aka: Bernstein polynomials, explicit polynomial approximants, probabilistic proof of Weierstrass, uniform approximation, verifiable approximation
- What: explicit polynomial approximants built from probability.
- Fits when: an explicit, verifiable approximation is needed.
- Lean: Mathlib: `bernsteinPolynomial`, `bernsteinApproximation_uniform`.
- Example: Bernstein's probabilistic proof of Weierstrass approximation ([Wikipedia: Bernstein polynomial](https://en.wikipedia.org/wiki/Bernstein_polynomial)).
- See also: T645, T616

### T650 Bellman function method
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: Bellman functions, dyadic induction, martingale inequalities, sharp constants, two-weight inequalities, Nazarov–Treil–Volberg, convexity condition
- What: encode an inequality by an extremal function of a few variables with a convexity condition; finding it proves the sharp inequality by induction on dyadic scales.
- Fits when: dyadic or martingale inequalities with sharp constants.
- Lean: a found Bellman function's convexity condition is a few-variable inequality (T128, T54).
- Example: Nazarov–Treil–Volberg on two-weight inequalities ([arXiv:math/9711209](https://arxiv.org/abs/math/9711209)).
- See also: T651, T383

### T651 Sparse domination
`bound` · stage: argue · signals: analytic, inequality
aka: sparse operators, sparse families of dyadic cubes, A₂ conjecture, sharp weighted inequalities, Muckenhoupt weights, Lerner
- What: dominate a singular integral by sums over sparse families of dyadic cubes, reducing weighted bounds to simple averaging operators.
- Fits when: sharp weighted inequalities.
- Lean: —
- Example: Lerner's simple proof of the A₂ conjecture ([arXiv:1202.2824](https://arxiv.org/abs/1202.2824)); vector-valued extension ([arXiv:2003.02233](https://arxiv.org/abs/2003.02233)).
- See also: T633, T650
