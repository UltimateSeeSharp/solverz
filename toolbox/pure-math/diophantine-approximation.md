# Diophantine approximation and transcendence
Irrationality and transcendence proofs, auxiliary polynomials and functions, linear forms in logarithms, the subspace theorem, and potential theory for algebraic integers.

### T540 Liouville-type constructions
`prove` `find` · stage: construct · signals: analytic, integers, construction
aka: Liouville numbers, Liouville's constant, very well approximable numbers, explicit transcendental numbers, badly approximable algebraic numbers
- What: algebraic numbers are badly approximable, so very well approximable numbers are transcendental.
- Fits when: building explicit transcendental numbers.
- Lean: Mathlib `Liouville.transcendental` and `transcendental_liouvilleNumber`.
- Example: Liouville's constant Σ10^{−n!} ([Wikipedia: Liouville number](https://en.wikipedia.org/wiki/Liouville_number)).
- See also: T541, T551

### T541 Auxiliary polynomial with many zeros (Thue–Siegel–Roth)
`bound` `prove` · stage: argue · signals: polynomial, integers, inequality
aka: Thue–Siegel–Roth theorem, Roth's theorem, approximation exponents, index of a polynomial, nonvanishing lemma
- What: builds a polynomial vanishing to high order at many approximations; a nonvanishing lemma gives a contradiction.
- Fits when: approximation exponents of algebraic numbers.
- Lean: —
- Example: Roth's theorem: algebraic α has |α − p/q| > q^{−2−ε} for large q ([Wikipedia: Roth's theorem](https://en.wikipedia.org/wiki/Roth's_theorem)).
- See also: T542, T393, T545

### T542 Siegel's lemma
`find` `prove` · stage: argue · signals: integers, matrix, construction
aka: small integer solutions, underdetermined linear systems, pigeonhole for integer vectors, auxiliary polynomials with integer coefficients
- What: an underdetermined integer linear system has a small nonzero integer solution (pigeonhole).
- Fits when: constructing auxiliary functions with integer coefficients.
- Lean: Mathlib `Int.Matrix.exists_ne_zero_int_vec_norm_le` (NumberTheory/SiegelsLemma.lean).
- Example: auxiliary polynomials in transcendence proofs ([Wikipedia: Siegel's lemma](https://en.wikipedia.org/wiki/Siegel's_lemma)).
- See also: T325, T541, T543

### T543 Auxiliary functions (Hermite–Lindemann–Gelfond–Schneider)
`prove` · stage: argue · signals: analytic, integers, impossibility
aka: Hermite's proof for e, Lindemann–Weierstrass theorem, Gelfond–Schneider theorem, a^b transcendental, exponential polynomials, size versus integrality
- What: builds an exponential polynomial vanishing at many points; size and integrality clash.
- Fits when: transcendence of values of exponentials.
- Lean: Mathlib has the analytic part of Lindemann–Weierstrass (NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean).
- Example: transcendence of e and π; Gelfond–Schneider for a^b ([Wikipedia: Lindemann–Weierstrass theorem](https://en.wikipedia.org/wiki/Lindemann–Weierstrass_theorem), [Wikipedia: Gelfond–Schneider theorem](https://en.wikipedia.org/wiki/Gelfond–Schneider_theorem)).
- See also: T542, T544, T305

### T544 Linear forms in logarithms (Baker)
`bound` `prove` · stage: argue · signals: integers, analytic, inequality
aka: Baker's theorem, Baker's method, effective lower bounds for |Σ b_i log α_i|, effective Diophantine bounds, class number problems
- What: explicit lower bounds for |Σ b_i log α_i| when it is nonzero.
- Fits when: effective bounds for exponential Diophantine equations.
- Lean: the bound is used as an input, and the remaining search is checked (T537).
- Example: Baker's effective solution of Thue and class number problems ([Wikipedia: Baker's theorem](https://en.wikipedia.org/wiki/Baker's_theorem)).
- See also: T536, T537, T526, T324

### T545 Schmidt subspace theorem
`prove` · stage: argue · signals: integers, matrix
aka: subspace theorem, S-unit equations, simultaneous approximation, finiteness in many variables, ineffective finiteness
- What: approximations to several linear forms concentrate on finitely many subspaces.
- Fits when: S-unit equations; finiteness in many variables (ineffective).
- Lean: —
- Example: finiteness of nondegenerate S-unit solutions ([Wikipedia: Subspace theorem](https://en.wikipedia.org/wiki/Subspace_theorem)).
- See also: T541, T551

### T546 "Almost rational" irrationality proofs
`prove` · stage: argue · signals: integers, analytic, impossibility
aka: irrationality criterion, good rational approximations, Apéry's theorem, ζ(3), Beukers' integrals, integer gaps
- What: finds integers q_n, p_n with 0 < |q_n x − p_n| → 0; integer gaps contradict rationality.
- Fits when: irrationality of specific constants with good rational approximations.
- Lean: Mathlib has the Dirichlet-type criterion `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.
- Example: Apéry's ζ(3) irrationality (and Beukers' integrals) ([Tricki: almost rational](https://www.tricki.org/article/To_prove_that_a_number_is_irrational_show_that_it_is_almost_rational), [Wikipedia: Apéry's theorem](https://en.wikipedia.org/wiki/Apéry's_theorem)).
- See also: T547, T548, T61

### T547 Integral (Niven-type) proofs
`prove` · stage: argue · signals: analytic, integers, impossibility
aka: Niven's proof, Cartwright's proof, irrationality of π, e^r irrational, polynomial-weighted integrals, positive integer tending to 0
- What: an integral with a polynomial weight is a positive integer yet tends to 0.
- Fits when: irrationality of π, e^r, values of nice special functions.
- Lean: Mathlib `irrational_pi`, via Cartwright's integral proof.
- Example: Niven's proof that π is irrational ([Wikipedia: Proof that π is irrational](https://en.wikipedia.org/wiki/Proof_that_π_is_irrational)).
- See also: T546

### T548 Hypergeometric linear forms and dimension counting
`prove` · stage: argue · signals: integers, analytic, matrix
aka: Ball–Rivoal theorem, odd zeta values, ζ(2n+1), linear forms in zeta values, dimension of ℚ-span
- What: many linear forms in zeta values with small coefficients force a large ℚ-span.
- Fits when: "infinitely many, or at least one, of these values is irrational".
- Lean: —
- Example: Rivoal (and Ball–Rivoal): infinitely many ζ(2n+1) are irrational ([arXiv:math/0008051](https://arxiv.org/abs/math/0008051)).
- See also: T546, T398

### T549 Arithmetic holonomy bounds
`prove` · stage: argue · signals: sequence, analytic, integers
aka: Borel–Dwork, Pólya–Bertrandias, holonomic power series with integer coefficients, unbounded denominators conjecture, Calegari–Dimitrov–Tang, rationality criteria, L(2, χ_{−3})
- What: a holonomic power series with integer coefficients and enough analytic room is rational or algebraic; potential theory measures the room.
- Fits when: irrationality and rationality criteria for generating functions.
- Lean: —
- Example: Calegari–Dimitrov–Tang: the unbounded denominators conjecture; irrationality of L(2, χ_{−3}) ([arXiv:2109.09040](https://arxiv.org/abs/2109.09040), [arXiv:2408.15403](https://arxiv.org/abs/2408.15403)).
- See also: T550, T554

### T550 Potential theory for algebraic integers
`bound` `prove` · stage: argue · signals: integers, polynomial, analytic
aka: capacity, transfinite diameter, equilibrium measures, Schur–Siegel–Smyth trace problem, totally positive algebraic integers
- What: capacity and equilibrium measures decide which distributions of conjugates are possible.
- Fits when: trace and height problems for totally real or totally positive integers.
- Lean: —
- Example: Smith's disproof of the Schur–Siegel–Smyth trace conjecture: infinitely many totally positive α with tr(α) < 1.89831·deg(α) ([arXiv:2111.12660](https://arxiv.org/abs/2111.12660)).
- See also: T549

### T551 Combinatorics of expansions plus the subspace theorem
`prove` · stage: argue · signals: sequence, integers, regular-structure
aka: automatic numbers, subword complexity, digit expansions, Adamczewski–Bugeaud, transcendence of automatic expansions
- What: low subword complexity of digit expansions plus Schmidt's subspace theorem forces transcendence.
- Fits when: numbers defined by automatic or low-complexity digit rules.
- Lean: —
- Example: Adamczewski–Bugeaud: an irrational number with automatic expansion in an integer base is transcendental ([Wikipedia: Automatic sequence](https://en.wikipedia.org/wiki/Automatic_sequence), [Wikipedia: Subspace theorem](https://en.wikipedia.org/wiki/Subspace_theorem)).
- See also: T545, T21

### T552 Ax–Schanuel functional transcendence
`prove` · stage: argue · signals: analytic, arithmetic-geometry
aka: Ax's theorem, Schanuel's conjecture, function-field Schanuel, unlikely intersections, o-minimal counting
- What: functional analogues of Schanuel's conjecture hold and feed o-minimal counting.
- Fits when: unlikely-intersection problems.
- Lean: —
- Example: Ax's theorem as the function-field Schanuel ([Wikipedia: Schanuel's conjecture](https://en.wikipedia.org/wiki/Schanuel's_conjecture)).
- See also: T756
