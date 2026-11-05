# Analytic number theory
Primes and arithmetic functions by complex analysis, exponential and character sums, mean values, zero density, multiplicative functions and explicit estimates.

### T477 Complex-analytic method (zero-free regions)
`prove` `bound` · stage: argue · signals: integers, analytic, asymptotic
aka: contour shifting, Perron's formula, L-functions, zeta function, de la Vallée Poussin zero-free region, prime number theorem, Dirichlet series
- What: writes the counting function as a contour integral of an L-function, shifts the contour and uses a zero-free region.
- Fits when: asymptotics for primes or arithmetic functions with Dirichlet series.
- Lean: Mathlib `riemannZeta` and `riemannZeta_ne_zero_of_one_le_re` (nonvanishing on Re s ≥ 1); the contour argument by hand.
- Example: the prime number theorem (Hadamard, de la Vallée Poussin) ([Wikipedia: Prime number theorem](https://en.wikipedia.org/wiki/Prime_number_theorem), [Tricki: Shift the contour of integration](https://www.tricki.org/article/Shift_the_contour_of_integration)).
- See also: T478, T490, T696

### T478 Tauberian theorems
`prove` · stage: argue · signals: analytic, sequence, asymptotic
aka: Wiener–Ikehara, Newman's proof, Hardy–Littlewood Tauberian, Karamata, boundary behaviour of Dirichlet and power series
- What: deduces asymptotics of coefficients from boundary behaviour of the generating Dirichlet or power series.
- Fits when: only analytic continuation or nonvanishing on the boundary is known.
- Lean: —
- Example: Wiener–Ikehara and Newman's short proof of the prime number theorem ([Wikipedia: Wiener–Ikehara theorem](https://en.wikipedia.org/wiki/Wiener–Ikehara_theorem), [Wikipedia: Prime number theorem](https://en.wikipedia.org/wiki/Prime_number_theorem)).
- See also: T477, T643

### T479 Characters and orthogonality
`prove` · stage: argue · signals: integers, group, congruence
aka: Dirichlet characters, orthogonality relations, detecting residue classes, L(1, χ) ≠ 0, primes in arithmetic progressions, Dirichlet's theorem
- What: detects a residue class by averaging Dirichlet characters; reduces the problem to nonvanishing of L(1, χ).
- Fits when: primes or arithmetic objects in congruence classes.
- Lean: Mathlib `DirichletCharacter.LFunction_apply_one_ne_zero` and Dirichlet's theorem `Nat.forall_exists_prime_gt_and_modEq` (LSeries/PrimesInAP.lean).
- Example: Dirichlet's theorem on primes in arithmetic progressions ([Wikipedia: Dirichlet's theorem](https://en.wikipedia.org/wiki/Dirichlet's_theorem_on_arithmetic_progressions)).
- See also: T487, T565, T529

### T480 Hardy–Littlewood circle method
`prove` `bound` · stage: argue · signals: integers, additive, asymptotic
aka: major and minor arcs, exponential sums, Waring's problem, Goldbach-type problems, Vinogradov's three-primes theorem, Diophantine equations in many variables, singular series
- What: writes the count as an integral of an exponential sum; major arcs give the main term, minor arcs need savings.
- Fits when: additive problems (Waring, Goldbach-type, Diophantine equations in many variables).
- Lean: —
- Example: Vinogradov's three-primes theorem and Waring's problem ([Wikipedia: Circle method](https://en.wikipedia.org/wiki/Hardy–Littlewood_circle_method), [Wikipedia: Vinogradov's theorem](https://en.wikipedia.org/wiki/Vinogradov's_theorem)).
- See also: T481, T482, T484, T557

### T481 Explicit circle method with heavy verification
`prove` · stage: argue · signals: integers, additive, inequality
aka: explicit constants, sufficiently large made effective, ternary Goldbach, numerical verification of small cases, interval arithmetic for constants
- What: makes every constant explicit so the remaining range is checkable by computer.
- Fits when: an "all sufficiently large n" theorem must become "all n".
- Lean: the explicit analysis by hand, the finite range kernel-checked (T42, T122); feasible only when the range stays kernel-small.
- Example: Helfgott's proof of the ternary Goldbach conjecture ([arXiv:1312.7748](https://arxiv.org/abs/1312.7748)).
- See also: T324, T480, T42, T64

### T482 Weyl differencing, van der Corput and equidistribution
`prove` `bound` · stage: argue · signals: analytic, sequence, integers
aka: Weyl's inequality, Weyl criterion, van der Corput lemma, van der Corput differencing, square and shift, polynomial phases, uniform distribution mod 1, equidistribution of polynomial sequences
- What: tests equidistribution against characters (Weyl criterion); squaring and shifting (Cauchy–Schwarz) lowers the degree of a polynomial phase.
- Fits when: exponential sums with polynomial phases; distribution of polynomial or dynamical sequences mod 1.
- Lean: —
- Example: Weyl's inequality for polynomial phases; van der Corput's equidistribution lemma; equidistribution of polynomial sequences ([Wikipedia: Weyl's inequality](https://en.wikipedia.org/wiki/Weyl's_inequality), [Tricki: Square and rearrange](https://www.tricki.org/article/Square_and_rearrange), [Tricki: van der Corput lemma](https://www.tricki.org/article/The_van_der_Corput_lemma_for_equidistribution), [Wikipedia: Weyl's criterion](https://en.wikipedia.org/wiki/Weyl's_criterion), [Wikipedia: Equidistribution theorem](https://en.wikipedia.org/wiki/Equidistribution_theorem)).
- See also: T483, T484, T606, T823

### T483 Benford's law and leading digits
`prove` `compute` · stage: argue · signals: integers, sequence, exact-value
aka: first-digit law, leading digits, significant digits, log10 mod 1, powers of 2, Fibonacci numbers, factorials, scale invariance, base invariance
- What: the leading digit d has frequency log_b(1 + 1/d) when log_b of the sequence is equidistributed mod 1; for powers k^n this holds exactly when log10 k is irrational, by the equidistribution theorem.
- Fits when: questions about leading digits or mantissas of exponential or multiplicative sequences.
- Lean: leading digits of a finite range by `decide +kernel`; the limit law needs irrationality of log10 k and an equidistribution proof, which Mathlib lacks (no Weyl criterion).
- Example: the Fibonacci numbers, the factorials and the powers of 2 follow the law exactly in the limit; scale-invariant first-digit distributions are always Benford ([Wikipedia: Benford's law](https://en.wikipedia.org/wiki/Benford%27s_law)).
- See also: T482, T828

### T484 Vinogradov mean values (efficient congruencing, decoupling)
`bound` · stage: argue · signals: integers, analytic, inequality
aka: Vinogradov's mean value theorem, main conjecture, efficient congruencing, Wooley, Bourgain–Demeter–Guth, decoupling, moments of Weyl sums
- What: bounds moments of Weyl sums sharply by p-adic nesting or by Fourier decoupling.
- Fits when: high moments of exponential sums.
- Lean: —
- Example: Wooley's efficient congruencing and Bourgain–Demeter–Guth's proof of the main conjecture for degree > 3 ([arXiv:1101.0574](https://arxiv.org/abs/1101.0574), [arXiv:1512.01565](https://arxiv.org/abs/1512.01565)).
- See also: T482, T639

### T485 Type I/II decompositions (Vaughan, Heath-Brown)
`bound` `prove` · stage: argue · signals: integers, analytic
aka: Vaughan's identity, Heath-Brown identity, bilinear sums, Type I and Type II sums, von Mangoldt function, primes with missing digits
- What: splits Λ(n) into pieces where one variable is smooth (Type I) or two are balanced (Type II, bilinear).
- Fits when: sums of primes against oscillating or structured weights.
- Lean: Mathlib `ArithmeticFunction.vonMangoldt`; the identity itself is a finite algebraic manipulation.
- Example: Vinogradov's three-primes; Maynard's primes with a missing decimal digit ([Wikipedia: Vaughan's identity](https://en.wikipedia.org/wiki/Vaughan's_identity), [arXiv:1604.01041](https://arxiv.org/abs/1604.01041)).
- See also: T509, T480

### T486 Exponential sums from algebraic geometry
`bound` · stage: argue · signals: finite-field, arithmetic-geometry, inequality
aka: Weil bound, Deligne's bound, Kloosterman sums, character sums of polynomials, square-root cancellation, complete sums over F_p
- What: Weil and Deligne bounds give square-root cancellation for complete sums.
- Fits when: Kloosterman sums, character sums of polynomials, sums over varieties over F_p.
- Lean: a specific complete sum over a small field by `decide +kernel`.
- Example: Weil's bound for Kloosterman sums ([Wikipedia: Kloosterman sum](https://en.wikipedia.org/wiki/Kloosterman_sum), [Wikipedia: Weil conjectures](https://en.wikipedia.org/wiki/Weil_conjectures)).
- See also: T487, T596, T559

### T487 Character-sum bounds (Pólya–Vinogradov, Burgess)
`bound` · stage: argue · signals: finite-field, integers, inequality
aka: incomplete character sums, Pólya–Vinogradov inequality, Burgess bound, least quadratic non-residue, primitive roots, short intervals mod p
- What: nontrivial bounds for incomplete character sums, Burgess's via Weil's results.
- Fits when: least nonresidues, primitive roots, short-interval equidistribution mod p.
- Lean: Mathlib has `gaussSum` and `legendreSym` for the algebra; a bound for one modulus by `decide +kernel`.
- Example: Pólya–Vinogradov (1918) and Burgess ([Wikipedia: Character sum](https://en.wikipedia.org/wiki/Character_sum)).
- See also: T486, T496, T479

### T488 Large sieve inequality
`bound` · stage: argue · signals: integers, analytic, inequality
aka: large sieve, almost orthogonality, well-spaced frequencies, mean values of Dirichlet polynomials, averaging over moduli
- What: an almost-orthogonality inequality bounding a sequence's mass across many residue classes or frequencies.
- Fits when: averaging over moduli; sieving many classes; mean values of Dirichlet polynomials.
- Lean: —
- Example: the large sieve and its use for Bombieri–Vinogradov ([Wikipedia: Large sieve](https://en.wikipedia.org/wiki/Large_sieve), [Wikipedia: Bombieri–Vinogradov theorem](https://en.wikipedia.org/wiki/Bombieri–Vinogradov_theorem)).
- See also: T489, T510, T638

### T489 GRH on average (Bombieri–Vinogradov)
`bound` · stage: argue · signals: integers, congruence
aka: Bombieri–Vinogradov theorem, level of distribution 1/2, primes in progressions for almost all moduli, Elliott–Halberstam conjecture
- What: primes are well distributed in progressions for almost all moduli up to √x.
- Fits when: a sieve or circle method needs level of distribution 1/2.
- Lean: —
- Example: the Bombieri–Vinogradov theorem itself, proved with the large sieve, as the level-1/2 input of sieve theory ([Wikipedia: Bombieri–Vinogradov theorem](https://en.wikipedia.org/wiki/Bombieri–Vinogradov_theorem), [Wikipedia: Large sieve](https://en.wikipedia.org/wiki/Large_sieve)).
- See also: T488, T507

### T490 Explicit formula
`prove` `bound` · stage: argue · signals: integers, analytic
aka: Riemann–von Mangoldt explicit formula, Weil explicit formula, sums over zeta zeros, oscillation of ψ(x), Chebyshev bias
- What: expresses prime sums as sums over zeta zeros, turning prime questions into zero-distribution questions.
- Fits when: oscillation of ψ(x), Chebyshev bias, explicit bounds.
- Lean: Mathlib defines `Chebyshev.psi` and `Chebyshev.theta`.
- Example: Riemann–von Mangoldt explicit formula ([Wikipedia: Explicit formulae for L-functions](https://en.wikipedia.org/wiki/Explicit_formulae_for_L-functions)).
- See also: T477, T491

### T491 Large values and zero density estimates
`bound` · stage: argue · signals: integers, analytic, inequality
aka: zero density, density hypothesis, large values of Dirichlet polynomials, primes in short intervals, Guth–Maynard
- What: bounds how often Dirichlet polynomials are large, hence how many zeros lie off the critical line.
- Fits when: primes in short intervals, density hypotheses.
- Lean: —
- Example: Guth–Maynard's zero density bound and primes in intervals of length x^{17/30+o(1)} ([arXiv:2405.20552](https://arxiv.org/abs/2405.20552)).
- See also: T490, T494

### T492 Moments and mollifiers
`bound` `prove` · stage: argue · signals: analytic, integers
aka: mollifier, moments of L-functions, proportion of zeros on the critical line, Selberg, Levinson, Conrey, nonvanishing of L-values
- What: computes moments of L-functions, damped by a mollifier, to force zeros on the line or nonvanishing.
- Fits when: proportions of zeros on the critical line or of nonvanishing L-values.
- Lean: —
- Example: Selberg, Levinson and Conrey proportions of zeta zeros on the critical line ([Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)).
- See also: T493, T558

### T493 Amplification (Duke–Friedlander–Iwaniec)
`bound` · stage: argue · signals: analytic, arithmetic-geometry, inequality
aka: DFI amplification, amplifier, subconvexity, family averages, sup norms of eigenfunctions, Rankin–Selberg L-functions
- What: bounds one L-value by a family average weighted to amplify it, then applies a trace formula.
- Fits when: subconvexity; sup norms of eigenfunctions.
- Lean: —
- Example: Herman's Rankin–Selberg subconvexity via DFI amplification ([arXiv:1303.4459](https://arxiv.org/abs/1303.4459)).
- See also: T621, T559, T492

### T494 Multiplicative functions in short intervals (Matomäki–Radziwiłł)
`bound` `prove` · stage: argue · signals: integers, analytic
aka: Matomäki–Radziwiłł theorem, Liouville function, Möbius function, short intervals, Dirichlet polynomial factorization, bounded multiplicative functions
- What: compares short and long averages via Dirichlet polynomial factorization and large-value estimates.
- Fits when: bounded multiplicative functions; Liouville or Möbius in short intervals.
- Lean: Mathlib defines `ArithmeticFunction.moebius` and the Liouville function.
- Example: Liouville averages over almost all intervals of length h → ∞ ([arXiv:1501.04585](https://arxiv.org/abs/1501.04585)).
- See also: T495, T496, T491

### T495 Entropy decrement
`prove` · stage: argue · signals: integers, random
aka: entropy decrement argument, logarithmic averaging, logarithmic Chowla, Elliott conjecture, Erdős discrepancy problem, correlations of multiplicative functions
- What: uses logarithmic averaging and an information-theoretic argument to find scales where correlations reduce to simpler ones.
- Fits when: correlations of multiplicative functions (Chowla, Elliott).
- Lean: —
- Example: Tao's logarithmic two-point Chowla/Elliott and the Erdős discrepancy problem ([arXiv:1509.05422](https://arxiv.org/abs/1509.05422), [arXiv:1509.05363](https://arxiv.org/abs/1509.05363)).
- See also: T494, T364, T1

### T496 Pretentiousness
`bound` `prove` · stage: argue · signals: integers, analytic
aka: pretentious distance, Granville–Soundararajan, mean values of multiplicative functions, large character sums, characters of odd order
- What: measures distances between multiplicative functions; a large sum forces the function to pretend to be a simple character.
- Fits when: mean values of multiplicative functions; large character sums.
- Lean: —
- Example: Granville–Soundararajan improve Pólya–Vinogradov for characters of odd bounded order ([arXiv:math/0503113](https://arxiv.org/abs/math/0503113)).
- See also: T487, T494

### T497 Probabilistic number theory (Turán–Kubilius)
`prove` `bound` · stage: argue · signals: integers, random, asymptotic
aka: Erdős–Kac theorem, Turán–Kubilius inequality, Hardy–Ramanujan normal order, ω(n), additive functions, limit laws, nearly independent indicators
- What: treats ω(n) as a sum of nearly independent indicators; variance and moment computations give limit laws.
- Fits when: the distribution of additive functions.
- Lean: Mathlib defines ω as `ArithmeticFunction.cardDistinctFactors`.
- Example: Erdős–Kac theorem; Hardy–Ramanujan normal order via Turán–Kubilius ([Wikipedia: Erdős–Kac theorem](https://en.wikipedia.org/wiki/Erdős–Kac_theorem), [Wikipedia: Turán–Kubilius inequality](https://en.wikipedia.org/wiki/Turán–Kubilius_inequality)).
- See also: T781, T377

### T498 Elementary Chebyshev-type estimates
`bound` `prove` · stage: argue · signals: integers, inequality
aka: Chebyshev bounds, central binomial coefficients, Bertrand's postulate, Erdős's proof, primorial bounds, θ(x) ≤ x log 4
- What: bounds primes using the divisibility of central binomial coefficients.
- Fits when: explicit, fully elementary prime bounds (good for formalization).
- Lean: Mathlib `Nat.exists_prime_lt_and_le_two_mul` (Bertrand) and `Chebyshev.theta_le_log4_mul_x`.
- Example: Erdős's proof of Bertrand's postulate ([Wikipedia: Bertrand's postulate](https://en.wikipedia.org/wiki/Bertrand's_postulate)).
- See also: T477, T324

### T499 Win-win from exceptional zeros (Deuring–Heilbronn)
`prove` · stage: argue · signals: integers, analytic
aka: Siegel zeros, exceptional characters, Deuring–Heilbronn phenomenon, zero repulsion, Linnik's theorem, least prime in a progression, class number bounds
- What: a Siegel zero would repel other zeros, which helps the other case.
- Fits when: the result can be proved both with and without an exceptional character.
- Lean: —
- Example: Linnik's theorem on the least prime in a progression; class number results ([Wikipedia: Siegel zero](https://en.wikipedia.org/wiki/Siegel_zero), [Wikipedia: Linnik's theorem](https://en.wikipedia.org/wiki/Linnik's_theorem)).
- See also: T533, T479

### T500 Partial summation, smoothing and Mellin transforms
`bound` · stage: argue · signals: analytic, integers
aka: Abel summation, summation by parts, smooth weights, Mellin inversion, sharp cutoffs, Fourier expansion of cutoffs
- What: moves between weighted and sharp sums; smooth cutoffs give rapidly decaying transforms.
- Fits when: sharp cutoffs make error terms ugly.
- Lean: Mathlib `sum_mul_eq_sub_sub_integral_mul` (NumberTheory/AbelSummation.lean) and `mellin`.
- Example: Abel summation and smoothed sums throughout analytic number theory ([Wikipedia: Abel's summation formula](https://en.wikipedia.org/wiki/Abel's_summation_formula), [Tricki: Use Fourier expansion to eliminate nasty cutoffs](https://www.tricki.org/article/Use_Fourier_expansion_to_eliminate_nasty_cutoffs), [Wikipedia: Mellin transform](https://en.wikipedia.org/wiki/Mellin_transform)).
- See also: T648, T477

### T501 Beurling–Selberg extremal functions
`bound` · stage: argue · signals: analytic, inequality
aka: majorants and minorants of exponential type, band-limited functions, Selberg's majorant, Erdős–Turán inequality, Hilbert-type inequalities, Gaussian subordination, box minorant problem
- What: majorants and minorants of exponential type with the least L¹ error, bracketing an indicator.
- Fits when: sharp large-sieve, Erdős–Turán and Hilbert-type inequalities; LP-style bounds with Fourier support constraints.
- Lean: —
- Example: Carneiro–Littmann–Vaaler's Gaussian subordination ([arXiv:1008.4969](https://arxiv.org/abs/1008.4969)); the box minorant problem via LP bounds ([arXiv:1702.04579](https://arxiv.org/abs/1702.04579)).
- See also: T488, T644, T50

### T502 GCD graphs and compression in metric Diophantine approximation
`prove` · stage: argue · signals: integers, graph, analytic
aka: Duffin–Schaeffer conjecture, GCD graphs, Koukoulopoulos–Maynard, zero-one laws, overlap of approximation sets, iterative compression
- What: controls overlaps of approximation sets via a graph on denominators weighted by gcds, iteratively compressed.
- Fits when: zero-one laws for approximation with arbitrary ψ.
- Lean: Mathlib has Gallagher's zero-one law `addWellApproximable_ae_empty_or_univ` (NumberTheory/WellApproximable.lean); the GCD-graph argument by hand.
- Example: Koukoulopoulos–Maynard's proof of the Duffin–Schaeffer conjecture ([arXiv:1907.04593](https://arxiv.org/abs/1907.04593)).
- See also: T775, T482

### T503 Fourier-analytic density arguments for Egyptian fractions
`prove` · stage: argue · signals: integers, additive, dense
aka: unit fractions, Egyptian fractions, Erdős–Graham problems, smooth numbers, Bloom's theorem, sums of reciprocals in dense sets
- What: smooth-number and circle-method estimates find unit-fraction representations inside dense sets.
- Fits when: Erdős–Graham-type problems on sums of reciprocals.
- Lean: the main theorem was fully checked in Lean 3 by Bloom and Mehta.
- Example: Bloom: every set of positive upper density contains S with Σ_{n∈S} 1/n = 1 ([arXiv:2112.03726](https://arxiv.org/abs/2112.03726), [JEMS paper with Lean appendix](https://ems.press/journals/jems/articles/14297980), [Lean Zulip announcement](https://leanprover-community.github.io/archive/stream/113488-general/topic/Density.20conjecture.20on.20unit.20fractions.html)).
- See also: T480, T412

### T504 Distortion method for covering systems
`prove` · stage: argue · signals: integers, congruence, random, impossibility
aka: covering systems, distortion method, minimum modulus problem, Hough's theorem, reweighted probability measures
- What: reweights the probability measure step by step so the uncovered mass stays positive.
- Fits when: proving that systems of congruences cannot cover Z under size constraints.
- Lean: —
- Example: Hough's solution of Erdős' minimum modulus problem for covering systems ([arXiv:1307.0874](https://arxiv.org/abs/1307.0874), [Wikipedia: Covering system](https://en.wikipedia.org/wiki/Covering_system)).
- See also: T511, T374
