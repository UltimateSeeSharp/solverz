# Algebraic number theory and Diophantine equations
Local and global obstructions, descent, factorization in number rings, p-adic methods, rational points on curves, the modular method, effective bounds that end in a finite search, and multiplicative-function equations.

### T512 Local obstructions
`prove` · stage: argue · signals: integers, congruence, impossibility
aka: congruence obstructions, no solutions mod m, real solvability, p-adic obstruction, local check as a finite certificate, sums of squares mod 4 and 8, first test for any Diophantine equation
- What: shows there are no solutions mod some m or over ℝ; the obstruction is a finite computation.
- Fits when: the first test for any Diophantine equation; nonexistence of integer or rational solutions.
- Lean: the residue table by `decide +kernel` over `ZMod m`; `omega` for small moduli.
- Example: x² + y² = 3z² has no nontrivial rational solution (reduce mod 3 and descend, or mod 4 for a primitive solution) ([Wikipedia: Hasse principle](https://en.wikipedia.org/wiki/Hasse_principle)).
- See also: T513, T515, T129

### T513 Local–global principle
`prove` · stage: argue · signals: integers, polynomial, arithmetic-geometry
aka: Hasse principle, Hasse–Minkowski theorem, quadratic forms over ℚ, p-adic solvability, everywhere locally soluble
- What: solvability everywhere locally implies global solvability for some classes (quadratic forms).
- Fits when: quadratic forms or varieties where the Hasse principle holds.
- Lean: —
- Example: the Hasse–Minkowski theorem ([Wikipedia: Hasse principle](https://en.wikipedia.org/wiki/Hasse_principle)).
- See also: T512, T514

### T514 Brauer–Manin obstruction
`prove` · stage: argue · signals: arithmetic-geometry, impossibility
aka: failure of the Hasse principle, Brauer group, Selmer's cubic, Manin obstruction, locally soluble but globally insoluble varieties
- What: a cohomological pairing explains failures of the Hasse principle.
- Fits when: locally soluble but globally insoluble varieties.
- Lean: —
- Example: Selmer's cubic 3x³ + 4y³ + 5z³ = 0 and Manin's explanation of such counterexamples ([Wikipedia: Brauer–Manin obstruction](https://en.wikipedia.org/wiki/Brauer–Manin_obstruction), [Wikipedia: Hasse principle](https://en.wikipedia.org/wiki/Hasse_principle)).
- See also: T513, T600

### T515 Descent
`prove` `bound` · stage: argue · signals: arithmetic-geometry, integers, impossibility
aka: Fermat's infinite descent, 2-descent, Selmer groups, Mordell–Weil theorem, rank bounds, twists, elliptic curves, x⁴ + y⁴ = z²
- What: maps rational points into a finite, computable group of twists to bound the rank; with heights it gives finite generation.
- Fits when: rational points on elliptic and higher-genus curves.
- Lean: Mathlib `AddCommGroup.fg_of_descent` (GroupTheory/Descent.lean, the abstract descent theorem) and Fermat's descent `not_fermat_42`, giving `fermatLastTheoremFour`; Mathlib has `WeierstrassCurve`.
- Example: the Mordell–Weil theorem (descent plus heights) ([Wikipedia: Mordell–Weil theorem](https://en.wikipedia.org/wiki/Mordell–Weil_theorem), [Wikipedia: Selmer group](https://en.wikipedia.org/wiki/Selmer_group)).
- See also: T531, T333, T522

### T516 Factorization in number rings and ideals
`prove` · stage: argue · signals: integers, group, impossibility
aka: rings of integers, unique factorization of ideals, Dedekind domains, class number, regular primes, Kummer, norm-form equations, Fermat's Last Theorem for regular primes
- What: factors the equation over a ring of integers; unique factorization of ideals replaces that of numbers.
- Fits when: x^n + y^n = z^n-type equations, norm-form equations.
- Lean: Mathlib `IsDedekindDomain` and `NumberField.classNumber`; `fermatLastTheoremThree` is proved in Mathlib via ℤ[ζ₃].
- Example: Kummer's proof of Fermat's Last Theorem for regular primes ([Wikipedia: Regular prime](https://en.wikipedia.org/wiki/Regular_prime)).
- See also: T517, T529

### T517 Cyclotomic and Galois-module arguments
`prove` · stage: argue · signals: integers, group
aka: cyclotomic fields, Galois-module structure of units and class groups, Catalan's conjecture, Mihăilescu's theorem, x^p − y^q = 1, roots of unity
- What: studies the equation inside cyclotomic fields using the Galois-module structure of units and class groups.
- Fits when: equations of the shape x^p − y^q = 1 or with roots of unity.
- Lean: Mathlib `IsCyclotomicExtension`; the argument by hand.
- Example: Mihăilescu's proof of Catalan's conjecture ([Wikipedia: Catalan's conjecture](https://en.wikipedia.org/wiki/Catalan's_conjecture)).
- See also: T516, T580

### T518 p-adic valuations, LTE and Hensel lifting
`prove` · stage: argue · signals: integers, congruence
aka: lifting-the-exponent lemma, LTE, p-adic valuation, ν_p, Hensel's lemma, divisibility of a^n − b^n, exponential Diophantine equations
- What: tracks valuations exactly; lifts solutions mod p to p-adic ones.
- Fits when: exponential Diophantine equations; divisibility of a^n − b^n.
- Lean: Mathlib `padicValNat`, LTE as `Nat.emultiplicity_pow_sub_pow` and `Int.emultiplicity_pow_sub_pow`, and `hensels_lemma`.
- Example: the lifting-the-exponent lemma; Hensel's lemma ([Wikipedia: Lifting-the-exponent lemma](https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma), [Wikipedia: Hensel's lemma](https://en.wikipedia.org/wiki/Hensel's_lemma)).
- See also: T534, T519

### T519 Newton polygons
`prove` · stage: argue · signals: polynomial, integers
aka: lower convex hull of valuations, p-adic root sizes, Eisenstein criterion, irreducibility of polynomials
- What: reads valuations of roots (and irreducibility) off the lower convex hull of coefficient valuations.
- Fits when: irreducibility of polynomials; p-adic root sizes.
- Lean: Mathlib `Polynomial.IsEisensteinAt` and `Polynomial.irreducible_of_eisenstein_criterion`.
- Example: Eisenstein-type irreducibility criteria ([Wikipedia: Newton polygon](https://en.wikipedia.org/wiki/Newton_polygon)).
- See also: T518

### T520 p-adic analytic interpolation (Skolem's method)
`prove` · stage: argue · signals: sequence, integers
aka: Skolem's method, Strassmann's theorem, Skolem–Mahler–Lech, zeros of linear recurrences, p-adic analytic functions, exponential Diophantine equations
- What: interpolates a recurrence or exponential by a p-adic analytic function; Strassmann bounds its zeros.
- Fits when: zeros of linear recurrences, exponential Diophantine equations.
- Lean: —
- Example: Skolem–Mahler–Lech: zero sets of linear recurrences are eventually periodic; its proofs are p-adic and non-constructive ([Wikipedia: Skolem–Mahler–Lech theorem](https://en.wikipedia.org/wiki/Skolem–Mahler–Lech_theorem), [Wikipedia: Strassmann's theorem](https://en.wikipedia.org/wiki/Strassmann's_theorem)).
- See also: T518, T544

### T521 Chabauty–Coleman and quadratic Chabauty
`prove` `compute` · stage: argue · signals: arithmetic-geometry, classification
aka: Chabauty's method, Coleman integration, rank less than genus, quadratic Chabauty, nonabelian Chabauty, all rational points on a curve, modular curves
- What: if rank < genus, rational points lie in the zeros of a p-adic integral; nonabelian refinements go further.
- Fits when: determining all rational points on a specific curve.
- Lean: —
- Example: Balakrishnan et al. determine the rational points of the split Cartan modular curve of level 13 ([Wikipedia: Chabauty's method](https://en.wikipedia.org/wiki/Chabauty's_method), [arXiv:1711.05846](https://arxiv.org/abs/1711.05846)).
- See also: T522, T523, T40

### T522 Mordell–Weil sieve
`prove` `compute` · stage: argue · signals: arithmetic-geometry, congruence, impossibility
aka: Bruin–Stoll, Jacobian, information mod many primes, no unknown rational points, genus ≥ 2 curves
- What: combines the Mordell–Weil group with information mod many primes to prove no unknown rational points exist.
- Fits when: rational points on curves of genus ≥ 2 with known Jacobian rank.
- Lean: the reductions mod each prime are finite computations (`decide +kernel`), the Mordell–Weil input is not formalized.
- Example: Bruin–Stoll ([arXiv:0906.1934](https://arxiv.org/abs/0906.1934)).
- See also: T521, T515

### T523 p-adic period maps
`prove` · stage: argue · signals: arithmetic-geometry
aka: Lawrence–Venkatesh, variation of Galois representations, Mordell's conjecture, Faltings's theorem, finiteness in families
- What: shows a family's Galois representations vary too little for many rational points.
- Fits when: finiteness theorems in families.
- Lean: —
- Example: Lawrence–Venkatesh's new proof of Mordell's conjecture ([arXiv:1807.02721](https://arxiv.org/abs/1807.02721), [Wikipedia: Faltings's theorem](https://en.wikipedia.org/wiki/Faltings's_theorem)).
- See also: T531, T521

### T524 Modular method (Frey curves and level lowering)
`prove` · stage: argue · signals: arithmetic-geometry, integers, impossibility
aka: Frey curve, Ribet's level lowering, Serre's conjecture, newforms, generalized Fermat equations a^p + b^q = c^r, Fermat's Last Theorem
- What: attaches an elliptic curve to a putative solution; modularity plus Ribet's level lowering forces a nonexistent newform.
- Fits when: generalized Fermat equations a^p + b^q = c^r and relatives.
- Lean: —
- Example: Wiles's proof of Fermat's Last Theorem ([Wikipedia: Wiles's proof](https://en.wikipedia.org/wiki/Wiles's_proof_of_Fermat's_Last_Theorem), [Wikipedia: Ribet's theorem](https://en.wikipedia.org/wiki/Ribet's_theorem)).
- See also: T525, T526, T554

### T525 Modularity lifting (Taylor–Wiles patching)
`prove` · stage: argue · signals: arithmetic-geometry, group
aka: R = T theorems, Taylor–Wiles patching, deformation rings, Hecke algebras, modularity theorem, semistable elliptic curves, automorphy of Galois representations
- What: proves R = T by patching deformation rings over auxiliary primes.
- Fits when: proving Galois representations are automorphic.
- Lean: —
- Example: the modularity theorem for semistable elliptic curves ([Wikipedia: Wiles's proof](https://en.wikipedia.org/wiki/Wiles's_proof_of_Fermat's_Last_Theorem), [Wikipedia: Modularity theorem](https://en.wikipedia.org/wiki/Modularity_theorem)).
- See also: T524, T561

### T526 Combined modular + Baker + computation
`prove` `compute` · stage: argue · signals: integers, sequence, classification
aka: perfect powers in recurrence sequences, Fibonacci perfect powers, Bugeaud–Mignotte–Siksek, modular method plus linear forms in logarithms, finite search
- What: the modular method bounds the exponent, linear forms in logs bound the rest, and a finite search closes it.
- Fits when: perfect powers in recurrence sequences.
- Lean: only the closing search is kernel-sized (`decide +kernel`); the modular and Baker steps are not formalized.
- Example: Bugeaud–Mignotte–Siksek: the only perfect powers among Fibonacci numbers are 0, 1, 8, 144 ([arXiv:math/0403046](https://arxiv.org/abs/math/0403046)).
- See also: T524, T544, T324

### T527 Geometry of numbers (Minkowski)
`prove` `find` · stage: argue · signals: integers, geometry
aka: Minkowski's convex body theorem, lattices, small solutions mod m, two-square and four-square theorems, Minkowski bound, class number finiteness
- What: a convex symmetric body of volume > 2^n·covolume contains a nonzero lattice point.
- Fits when: existence of small solutions to linear or quadratic conditions mod m.
- Lean: Mathlib `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`; `Nat.sum_four_squares` and `Nat.Prime.sq_add_sq` are proved.
- Example: Lagrange's four-square theorem and Fermat's two-square theorem via Minkowski ([Wikipedia: Minkowski's theorem](https://en.wikipedia.org/wiki/Minkowski's_theorem)).
- See also: T749, T46, T528

### T528 Counting orbits in fundamental domains (Bhargava)
`bound` `prove` · stage: argue · signals: arithmetic-geometry, geometry, group, asymptotic
aka: Bhargava's parametrizations, integral orbits, prehomogeneous vector spaces, average rank of elliptic curves, average size of Selmer groups and class groups, Bhargava–Shankar
- What: parametrizes arithmetic objects by integral orbits of a group action and counts lattice points in fundamental domains.
- Fits when: average sizes of class groups or Selmer groups.
- Lean: —
- Example: Bhargava–Shankar: the average rank of elliptic curves is bounded ([arXiv:1006.1002](https://arxiv.org/abs/1006.1002)).
- See also: T527, T747

### T529 Class field theory and Chebotarev density
`prove` · stage: argue · signals: integers, group, arithmetic-geometry
aka: Artin reciprocity, abelian extensions, Frobenius elements, Chebotarev density theorem, primes splitting in extensions, primes represented by forms
- What: abelian extensions are classified by ideal-class data; Frobenius elements equidistribute.
- Fits when: primes splitting in extensions; primes represented by forms.
- Lean: —
- Example: Artin reciprocity classifying abelian extensions; Chebotarev's equidistribution of Frobenius elements ([Wikipedia: Class field theory](https://en.wikipedia.org/wiki/Class_field_theory), [Wikipedia: Chebotarev's density theorem](https://en.wikipedia.org/wiki/Chebotarev's_density_theorem)).
- See also: T479, T516

### T530 Gauss sums and reciprocity laws
`prove` · stage: argue · signals: integers, finite-field, congruence
aka: quadratic reciprocity, Gauss sums, Zolotarev's lemma, Legendre and Jacobi symbols, higher reciprocity, sign determinations, counting lattice points two ways
- What: evaluates a sum two ways (or counts lattice points two ways) to relate residue symbols.
- Fits when: quadratic or higher reciprocity; sign determinations.
- Lean: Mathlib `legendreSym.quadratic_reciprocity`, `jacobiSym` and `gaussSum`; a symbol for given numbers by `decide +kernel`.
- Example: proofs of quadratic reciprocity via Gauss sums and via Zolotarev's permutation signs ([Wikipedia: Quadratic reciprocity](https://en.wikipedia.org/wiki/Quadratic_reciprocity), [Wikipedia: Gauss sum](https://en.wikipedia.org/wiki/Gauss_sum), [Wikipedia: Zolotarev's lemma](https://en.wikipedia.org/wiki/Zolotarev's_lemma)).
- See also: T327, T479

### T531 Heights
`prove` `bound` · stage: argue · signals: arithmetic-geometry, integers
aka: height functions, Northcott property, Weil height, Néron–Tate height, finiteness of points of bounded height, Mordell–Weil, Vojta
- What: measures arithmetic complexity; finitely many points of bounded height (Northcott) turn finiteness into bounds.
- Fits when: finiteness of rational points; Mordell–Weil.
- Lean: Mathlib NumberTheory/Height (heights on number fields, the Northcott property) and `AddCommGroup.fg_of_descent`.
- Example: Faltings' and Vojta-style proofs of Mordell's conjecture use heights ([Wikipedia: Height function](https://en.wikipedia.org/wiki/Height_function), [Wikipedia: Faltings's theorem](https://en.wikipedia.org/wiki/Faltings's_theorem)).
- See also: T515, T523

### T532 Euler systems and Iwasawa theory
`prove` · stage: argue · signals: arithmetic-geometry, group
aka: Kolyvagin's Euler system, Iwasawa theory, p-adic L-functions, towers of fields, Selmer group bounds, BSD-type results, Gross–Zagier
- What: compatible families of cohomology classes bound Selmer groups; towers of fields give p-adic L-functions.
- Fits when: BSD-type results; class group structure.
- Lean: —
- Example: Kolyvagin's Euler system for elliptic curves of analytic rank ≤ 1 (with Gross–Zagier) ([Wikipedia: Euler system](https://en.wikipedia.org/wiki/Euler_system), [Wikipedia: Iwasawa theory](https://en.wikipedia.org/wiki/Iwasawa_theory), [Wikipedia: Gross–Zagier theorem](https://en.wikipedia.org/wiki/Gross–Zagier_theorem)).
- See also: T515, T533

### T533 Heegner points and modular curves for class numbers
`prove` · stage: argue · signals: arithmetic-geometry, integers, classification
aka: Heegner points, Stark–Heegner theorem, class number one problem, imaginary quadratic fields, integral points on modular curves
- What: relates imaginary quadratic fields of small class number to integral points on modular curves.
- Fits when: class number problems.
- Lean: —
- Example: Heegner–Stark solution of the class number one problem ([Wikipedia: Stark–Heegner theorem](https://en.wikipedia.org/wiki/Stark–Heegner_theorem)).
- See also: T499, T532

### T534 Primitive divisors (Zsigmondy, Bilu–Hanrot–Voutier)
`prove` · stage: argue · signals: integers, sequence
aka: Zsigmondy's theorem, Bang's theorem, primitive prime divisors, Lucas sequences, Lehmer sequences, Bilu–Hanrot–Voutier, a^n − b^n
- What: every term beyond a small explicit index of a^n − b^n or a Lucas sequence has a new prime factor.
- Fits when: exponential equations whose terms must share prime factors.
- Lean: the finitely many exceptional terms by `decide +kernel`.
- Example: Zsigmondy's theorem ([Wikipedia: Zsigmondy's theorem](https://en.wikipedia.org/wiki/Zsigmondy's_theorem)).
- See also: T518, T535

### T535 σ-equations and perfect-number case analysis
`prove` `bound` · stage: argue · signals: integers, impossibility
aka: σ(n) = 2n, abundancy index σ(n)/n, perfect numbers, odd perfect numbers, multiperfect numbers, Euclid–Euler theorem, Euler's form p^e m², special prime, factor chains, multiplicativity of σ, σ(p^e) = (p^(e+1) − 1)/(p − 1)
- What: σ is multiplicative and σ(p^e) is explicit, so σ(N) = 2N forces divisibility: each p^e in N puts the primes of σ(p^e) into N; branching on primes and exponents (factor chains) and bounding the abundancy σ(N)/N closes each branch.
- Fits when: equations in σ or other multiplicative functions; lower bounds on hypothetical solutions (size, number of prime factors).
- Lean: Mathlib `Nat.Perfect`, `ArithmeticFunction.sigma`, `ArithmeticFunction.isMultiplicative_sigma`; Euclid–Euler is in Mathlib's Archive (Wiedijk100Theorems/PerfectNumbers.lean); each branch is a factorization and an inequality (`decide +kernel`, `norm_num`; primality by T43), one theorem per branch (T122).
- Example: Euler's form N = p^e m² with p ≡ e ≡ 1 mod 4; chains such as σ(3²) = 13, σ(13) = 2·7 force new primes; Ochem–Rao used factor chains to prove N > 10^1500 ([Ochem–Rao slides](https://www.lirmm.fr/~ochem/opn/opn_slide.pdf), [Wikipedia: Perfect number](https://en.wikipedia.org/wiki/Perfect_number)).
- See also: T534, T43, T44, T122

### T536 Thue equations via Baker
`prove` `compute` · stage: argue · signals: integers, polynomial, classification
aka: Thue equations, F(x, y) = m, binary forms of degree ≥ 3, effective bounds, linear forms in logarithms, finite search
- What: effective bounds on solutions of F(x, y) = m, then a finite search.
- Fits when: binary forms of degree ≥ 3.
- Lean: only the final search, once the bound is small (T537), by `decide +kernel`.
- Example: effective solution of Thue equations ([Wikipedia: Thue equation](https://en.wikipedia.org/wiki/Thue_equation), [Wikipedia: Baker's theorem](https://en.wikipedia.org/wiki/Baker's_theorem)).
- See also: T544, T537, T324

### T537 Baker–Davenport reduction
`prove` `compute` · stage: argue · signals: integers, sequence, classification
aka: Baker–Davenport lemma, reducing Baker bounds, LLL, continued fractions, exponential Diophantine equations in recurrences, Fibonacci and powers of 2
- What: after Baker gives a huge bound, LLL or continued fractions cut it to a small one in a few steps; then search.
- Fits when: exponential Diophantine equations in recurrences.
- Lean: only the last small search, by `decide +kernel`; the reduction step's arithmetic can be checked with `norm_num`.
- Example: Şiar–Keskin solve F_n − F_m = 2^a with linear forms in logs and Baker–Davenport ([arXiv:1712.10138](https://arxiv.org/abs/1712.10138)).
- See also: T544, T46, T324

### T538 Pell equations and continued fractions
`prove` `compute` · stage: argue · signals: integers, sequence
aka: Pell's equation, x² − Dy² = n, fundamental unit, fundamental solution, periodic continued fractions, convergents of √D, recurrences from Pell equations
- What: fundamental units from periodic continued fractions generate all solutions.
- Fits when: x² − Dy² = n and recurrences arising from it.
- Lean: Mathlib `Pell.Solution₁`, `Pell.exists_of_not_isSquare`, `Pell.IsFundamental`; a fundamental solution checked with `decide +kernel`.
- Example: solving Pell's equation ([Wikipedia: Pell's equation](https://en.wikipedia.org/wiki/Pell's_equation)).
- See also: T527, T46

### T539 Hilbert irreducibility
`prove` `find` · stage: argue · signals: polynomial, group
aka: Hilbert's irreducibility theorem, specialization, inverse Galois problem, prescribed Galois groups, thin sets
- What: specializing a parameter preserves irreducibility and the Galois group for most values.
- Fits when: constructing number fields with prescribed Galois groups; specialization arguments.
- Lean: —
- Example: a group realized as a Galois group over ℚ(X_1..X_r) is realized over ℚ by specialization ([Wikipedia: Hilbert's irreducibility theorem](https://en.wikipedia.org/wiki/Hilbert's_irreducibility_theorem)).
- See also: T580
