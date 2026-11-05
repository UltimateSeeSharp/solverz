# Algebraic geometry
Algebraic geometry and commutative algebra as proof tools: reduction mod p, transfer between fields, finiteness, intersection and dimension counts, point counts over finite fields, real roots.

### T585 Reduction mod p and spreading out
`prove` · stage: reformulate · signals: polynomial, finite-field
aka: spreading out, finitely generated subrings, reduction to finite fields, Ax–Grothendieck theorem, injective polynomial maps are surjective, use finite fields
- What: a statement over C follows from the same statement over finite fields via finitely generated subrings.
- Fits when: algebraic statements where finite fields make counting trivial.
- Lean: Mathlib: `ax_grothendieck_univ` (`FieldTheory/AxGrothendieck.lean`).
- Example: Ax–Grothendieck: injective polynomial maps C^n → C^n are surjective ([Tricki: Use finite fields](https://www.tricki.org/article/Use_finite_fields), [Wikipedia: Ax–Grothendieck theorem](https://en.wikipedia.org/wiki/Ax–Grothendieck_theorem)).
- See also: T586, T593

### T586 Lefschetz principle
`prove` · stage: reformulate · signals: polynomial, logic
aka: transfer principle, algebraically closed fields of characteristic 0, theory ACF_0, model completeness, C versus Q-bar, first-order transfer
- What: first-order statements true over one algebraically closed field of characteristic 0 hold over all.
- Fits when: moving between C, Q-bar and other algebraically closed fields.
- Lean: Mathlib: `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize` (`ModelTheory/Algebra/Field/IsAlgClosed.lean`).
- Example: transferring results from C to arbitrary characteristic-0 algebraically closed fields ([Wikipedia: Lefschetz principle](https://en.wikipedia.org/wiki/Lefschetz_principle)).
- See also: T585, T751

### T587 Non-constructive finiteness (Hilbert basis theorem)
`prove` · stage: argue · signals: polynomial, group
aka: Noetherian rings, Hilbert's basis theorem, Hilbert's finiteness theorem, finite generation of invariant rings, ascending chain condition
- What: Noetherianity gives finite generation without listing the generators.
- Fits when: finite generation of invariants or ideals.
- Lean: Mathlib: `Polynomial.isNoetherianRing`.
- Example: Hilbert's finiteness theorem for invariant rings ([Wikipedia: Hilbert's basis theorem](https://en.wikipedia.org/wiki/Hilbert's_basis_theorem)).
- See also: T568, T59

### T588 Bézout and intersection counting
`prove` `bound` · stage: argue · signals: polynomial, geometry, inequality
aka: Bézout's theorem, intersection multiplicity, degree bounds, plane curves, polynomial method incidences, joints, distinct distances
- What: two plane curves of degrees d and e without a common component meet in at most de points.
- Fits when: polynomial-method incidence bounds; rigidity of algebraic configurations.
- Lean: one-variable case `Polynomial.card_roots'`; Bézout for plane curves not found in Mathlib.
- Example: Bézout's theorem in the joints and distinct-distance proofs ([Wikipedia: Bézout's theorem](https://en.wikipedia.org/wiki/Bézout's_theorem)).
- See also: T396, T397, T59

### T589 Riemann–Roch dimension counts
`prove` `find` · stage: argue · signals: arithmetic-geometry, polynomial, exact-value
aka: Riemann–Roch theorem, linear systems, divisors, functions with prescribed poles, algebraic-geometry codes, Goppa codes, genus
- What: compute dimensions of spaces of functions or sections with prescribed poles.
- Fits when: existence of functions with given zeros and poles; codes from curves.
- Lean: — (Riemann–Roch not found in Mathlib).
- Example: the Riemann–Roch theorem ([Wikipedia: Riemann–Roch theorem](https://en.wikipedia.org/wiki/Riemann–Roch_theorem)).
- See also: T590, T596

### T590 Hilbert functions and dimension counting via incidence varieties
`prove` · stage: argue · signals: polynomial, geometry, exact-value
aka: Hilbert polynomial, Hilbert series, parameter counts, incidence correspondence, dimension of families, 27 lines on a cubic surface, polynomial method parameter counting
- What: compare dimensions of polynomial spaces with constraints; incidence correspondences compute dimensions of loci.
- Fits when: polynomial-method parameter counts; dimensions of families (lines on surfaces).
- Lean: Mathlib: `Polynomial.hilbertPoly` (`RingTheory/Polynomial/HilbertPoly.lean`); a parameter count is linear algebra (`Module.finrank`).
- Example: the 27 lines on a cubic surface via incidence varieties ([Tricki: Dimension counting via incidence varieties](https://www.tricki.org/article/Dimension_counting_via_incidence_varieties), [Wikipedia: Hilbert series](https://en.wikipedia.org/wiki/Hilbert_series_and_Hilbert_polynomial)).
- See also: T398, T393, T592

### T591 Tropicalization
`prove` `compute` · stage: reformulate · signals: polynomial, geometry, exact-value
aka: tropical geometry, min-plus semiring, max-plus, Newton polytope subdivisions, piecewise-linear shadows, degenerations, Mikhalkin correspondence, curve counting
- What: replace varieties by piecewise-linear shadows over the min-plus semiring.
- Fits when: counting curves, degenerations, combinatorial shadows of algebraic problems.
- Lean: Mathlib has the semiring `Tropical` (`Algebra/Tropical/`); tropical varieties not found.
- Example: Mikhalkin's tropical curve counting ([Wikipedia: Tropical geometry](https://en.wikipedia.org/wiki/Tropical_geometry)).
- See also: T592, T59

### T592 Schubert calculus
`compute` · stage: argue · signals: geometry, polynomial, exact-value
aka: Grassmannians, Chow ring, Schubert cycles, Littlewood–Richardson coefficients, enumerative geometry, lines meeting four lines
- What: enumerative questions become products in the cohomology of Grassmannians.
- Fits when: counting linear spaces meeting given ones.
- Lean: — (Mathlib has `RingTheory/Grassmannian.lean`; Schubert calculus not found).
- Example: exactly two lines meet four general lines in P^3, computed in the Chow ring of Gr(2,4) ([Wikipedia: Schubert calculus](https://en.wikipedia.org/wiki/Schubert_calculus)).
- See also: T591, T456

### T593 Characteristic-p methods (Frobenius, tight closure)
`prove` · stage: argue · signals: polynomial, finite-field
aka: Frobenius map, tight closure, F-singularities, reduction to characteristic p, Briançon–Skoda, Hochster–Roberts, Cohen–Macaulay invariant rings
- What: use the Frobenius map to prove statements in characteristic 0 by reduction to characteristic p.
- Fits when: commutative-algebra statements (Briançon–Skoda, Cohen–Macaulayness of invariant rings).
- Lean: Mathlib has `frobenius` and `CharP`; tight closure not found.
- Example: tight closure proofs of the Hochster–Roberts theorem ([Wikipedia: Tight closure](https://en.wikipedia.org/wiki/Tight_closure)).
- See also: T585

### T594 Real-root counting (Sturm, Descartes)
`prove` `compute` · stage: argue · signals: polynomial, analytic, exact-value, inequality
aka: Sturm sequences, Sturm's theorem, Descartes' rule of signs, sign variations, root isolation, interval isolation, root-counting certificates, positivity on an interval, univariate polynomial inequalities
- What: count real roots in an interval exactly by sign changes; a Sturm sequence or an isolation is a finite certificate of a root count or of positivity.
- Fits when: polynomial positivity or root location in one variable.
- Lean: Mathlib: `Polynomial.roots_countP_pos_le_signVariations` (Descartes), `Polynomial.sturmSeq` (Sturm sequence, without the root-count theorem); sign checks at rational points by `norm_num`.
- Example: Sturm's theorem and Descartes' rule of signs ([Wikipedia: Sturm's theorem](https://en.wikipedia.org/wiki/Sturm's_theorem), [Wikipedia: Descartes' rule of signs](https://en.wikipedia.org/wiki/Descartes'_rule_of_signs)).
- See also: T22, T54, T74

### T595 Newton's identities and symmetric functions
`prove` `compute` · stage: argue · signals: polynomial, matrix, identity
aka: power sums, elementary symmetric polynomials, Newton–Girard formulas, traces of matrix powers, eigenvalue traces, symmetric function theory
- What: move between power sums and elementary symmetric functions.
- Fits when: polynomial-method arguments over fields; traces of eigenvalues.
- Lean: Mathlib: `MvPolynomial.psum_eq_mul_esymm_sub_sum`, `MvPolynomial.mul_esymm_eq_sum` (`RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`).
- Example: Newton's identities ([Wikipedia: Newton's identities](https://en.wikipedia.org/wiki/Newton's_identities)).
- See also: T393, T582

### T596 Hasse–Weil point-count bounds
`prove` `find` · stage: argue · signals: arithmetic-geometry, finite-field, inequality, pseudorandom
aka: Hasse's theorem, Hasse–Weil bound, Weil bound, points on curves over F_q, elliptic curves over finite fields, quasirandom algebraic graphs, existence of configurations over F_q
- What: |#C(F_q) − (q + 1)| ≤ 2g√q for a curve of genus g; existence of points or configurations over F_q follows.
- Fits when: showing a finite-field configuration exists for large q; quasirandomness of algebraic graphs.
- Lean: — (the bound is not found in Mathlib); for one small q the point count by `decide +kernel`.
- Example: Hasse's theorem and the Hasse–Weil bound ([Wikipedia: Hasse's theorem on elliptic curves](https://en.wikipedia.org/wiki/Hasse%27s_theorem_on_elliptic_curves)).
- See also: T486, T589, T366
