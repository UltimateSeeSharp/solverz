# Groups, rings, fields and representations
Proof techniques of algebra: group actions, characters, transfer, free and geometric group theory, Galois theory, rings by idempotents and localization.

### T563 Group actions on a well-chosen set
`prove` · stage: argue · signals: group, congruence, symmetric
aka: orbit–stabilizer, fixed points mod p, Wielandt's proof, Sylow theorems, Cauchy's theorem, action on cosets, action on p-subsets, subgroups of small index
- What: let the group act on cosets, subsets or itself; orbit–stabilizer and fixed-point counts mod p give structure.
- Fits when: existence of subgroups or elements of a given order; normal subgroups of small index.
- Lean: Mathlib: `IsPGroup.card_modEq_card_fixedPoints`, `exists_prime_orderOf_dvd_card` (Cauchy), `card_sylow_modEq_one` and the `Sylow` API.
- Example: Cauchy's theorem and Sylow's theorems, with Wielandt's proof via the action on p-subsets ([Tricki: group acting on a finite set](https://www.tricki.org/article/Proving_results_by_letting_a_group_act_on_a_finite_set), [Wikipedia: Sylow theorems](https://en.wikipedia.org/wiki/Sylow_theorems)).
- See also: T564, T571, T315, T29

### T564 Induction on the order and minimal counterexamples in groups
`prove` · stage: argue · signals: group, classification, induction-stuck
aka: minimal counterexample, minimal simple group, local analysis, Feit–Thompson odd order theorem, solvability, complements, p-groups
- What: a minimal counterexample has every proper subgroup and quotient satisfying the claim.
- Fits when: solvability, existence of complements, p-group results.
- Lean: strong induction on `Nat.card G`; Mathlib proves Schur–Zassenhaus this way (`Subgroup.exists_right_complement'_of_coprime`).
- Example: local analysis in the Feit–Thompson odd order theorem ([Wikipedia: Feit–Thompson theorem](https://en.wikipedia.org/wiki/Feit–Thompson_theorem)).
- See also: T334, T563, T567

### T565 Character theory
`prove` · stage: argue · signals: group, integers, impossibility
aka: class functions, orthogonality relations, character table, integrality of characters, Burnside's p^a q^b theorem, Frobenius groups, Frobenius kernel, simple group recognition
- What: class functions and orthogonality give integrality and divisibility constraints invisible to subgroup arguments.
- Fits when: solvability, Frobenius groups, recognizing simple groups.
- Lean: Mathlib: `FDRep.char_orthonormal`, `Representation.isIntegral_character`; Burnside's p^a q^b theorem not found in Mathlib.
- Example: Burnside's p^a q^b theorem; Frobenius' theorem on Frobenius kernels, still with no proof avoiding characters ([Wikipedia: Burnside's theorem](https://en.wikipedia.org/wiki/Burnside's_theorem), [Wikipedia: Frobenius group](https://en.wikipedia.org/wiki/Frobenius_group)).
- See also: T569, T568, T29

### T566 Transfer homomorphism
`prove` · stage: argue · signals: group, impossibility
aka: transfer, Verlagerung, focal subgroup theorem, Burnside's normal p-complement theorem, p-nilpotency, nonsimplicity criteria
- What: map G to an abelian quotient of a subgroup to detect normal complements.
- Fits when: p-nilpotency and nonsimplicity criteria.
- Lean: Mathlib: `MonoidHom.transfer`, `ker_transferSylow_isComplement'` (Burnside's normal p-complement), `commutator_inf_eq_focalSubgroup`.
- Example: the focal subgroup theorem and Burnside's normal p-complement theorem ([Wikipedia: Transfer](https://en.wikipedia.org/wiki/Transfer_%28group_theory%29)).
- See also: T563, T565

### T567 Reduction to simple groups via the classification
`prove` · stage: argue · signals: group, classification
aka: CFSG, classification of finite simple groups, inductive conditions, McKay conjecture, character degrees, generation, fixed points, case by case over simple groups
- What: reduce a statement about all finite groups to "inductive conditions" on finite simple groups, then verify case by case.
- Fits when: global statements about finite groups (character degrees, generation, fixed points).
- Lean: — (the classification is not formalized); small simple groups only, by computation (T29).
- Example: Cabanes–Späth's proof of the McKay conjecture ([arXiv:2410.20392](https://arxiv.org/abs/2410.20392), [Wikipedia: Classification of finite simple groups](https://en.wikipedia.org/wiki/Classification_of_finite_simple_groups)).
- See also: T564, T565, T29

### T568 Averaging over the group (Maschke, Reynolds operator)
`prove` · stage: argue · signals: group, polynomial, symmetric
aka: Reynolds operator, Maschke's theorem, complete reducibility, invariant inner product, invariant rings, symmetrize a projection, averaging trick
- What: average a projection or form over a finite group to make it invariant.
- Fits when: complete reducibility, invariant inner products, invariant rings.
- Lean: Mathlib: `MonoidAlgebra.Submodule.exists_isCompl` (Maschke, `RepresentationTheory/Maschke.lean`).
- Example: Maschke's theorem ([Wikipedia: Maschke's theorem](https://en.wikipedia.org/wiki/Maschke's_theorem)).
- See also: T569, T587, T315

### T569 Schur's lemma and isotypic decomposition
`prove` · stage: argue · signals: group, matrix, symmetric
aka: intertwiners, commutant, isotypic components, irreducible representations, abelian groups have 1-dimensional irreducibles, block-diagonalizing symmetric operators
- What: intertwiners between irreducibles are scalars; any representation splits into isotypic parts.
- Fits when: computing commutants; diagonalizing operators that commute with a group.
- Lean: Mathlib: `LinearMap.bijective_or_eq_zero` for simple modules (`RingTheory/SimpleModule/Basic.lean`).
- Example: Schur's lemma and its corollaries for abelian groups ([Wikipedia: Schur's lemma](https://en.wikipedia.org/wiki/Schur's_lemma)).
- See also: T565, T570

### T570 Double centralizer (Schur–Weyl duality)
`prove` · stage: argue · signals: group, matrix, symmetric, product-structure
aka: Schur–Weyl duality, double commutant, tensor space, GL_n and S_k, polynomial representations, invariants of tensors
- What: the GL_n and S_k actions on tensor space determine each other's irreducibles.
- Fits when: polynomial representations, invariants of tensors.
- Lean: — (Schur–Weyl duality not found in Mathlib).
- Example: Schur–Weyl duality ([Wikipedia: Schur–Weyl duality](https://en.wikipedia.org/wiki/Schur–Weyl_duality)).
- See also: T569, T456

### T571 Class equation plus cyclotomic polynomials
`prove` · stage: argue · signals: group, polynomial, integers
aka: Witt's proof, Wedderburn's little theorem, finite division rings are fields, class equation, Φ_n(q), rigidity of finite structures
- What: compare the class equation with Φ_n(q) to force commutativity.
- Fits when: finite division rings and similar finite-structure rigidity.
- Lean: Mathlib: `littleWedderburn` (Witt's proof), `Group.card_center_add_sum_card_noncenter_eq_card`.
- Example: Witt's proof of Wedderburn's little theorem ([Wikipedia: Wedderburn's little theorem](https://en.wikipedia.org/wiki/Wedderburn's_little_theorem)).
- See also: T563

### T572 Golod–Shafarevich inequality
`prove` `find` · stage: argue · signals: group, construction
aka: pro-p groups, generators and relations, infinite class field towers, general Burnside problem, infinite finitely generated torsion groups
- What: a pro-p group with few relations relative to generators is infinite.
- Fits when: constructing infinite groups with finiteness properties; class field towers.
- Lean: — (not found in Mathlib).
- Example: a negative answer to the general Burnside problem; infinite class field towers ([Wikipedia: Golod–Shafarevich theorem](https://en.wikipedia.org/wiki/Golod–Shafarevich_theorem), [Wikipedia: Burnside problem](https://en.wikipedia.org/wiki/Burnside_problem)).
- See also: T573, T529

### T573 Lie-algebra methods for p-groups
`prove` · stage: argue · signals: group, classification
aka: associated Lie ring, Lie algebras of finite characteristic, Engel identities, restricted Burnside problem, Kostrikin, Zelmanov, bounded exponent
- What: pass from a group to an associated Lie ring and use identities in Lie algebras of finite characteristic.
- Fits when: finiteness and bounded-order questions about groups.
- Lean: Mathlib has Lie algebras (`Algebra/Lie/`, e.g. `Engel.lean`); the restricted Burnside problem is not there.
- Example: Kostrikin (prime exponent) and Zelmanov (arbitrary exponent, 1989) solved the restricted Burnside problem ([Wikipedia: Burnside problem](https://en.wikipedia.org/wiki/Burnside_problem)).
- See also: T572

### T574 Ping-pong lemma
`prove` · stage: argue · signals: group, construction
aka: free subgroups, table-tennis lemma, Klein's criterion, Tits alternative, linear groups, Schottky groups
- What: elements moving disjoint regions into each other generate a free group.
- Fits when: showing a group contains free subgroups.
- Lean: Mathlib: `Monoid.CoprodI.lift_injective_of_ping_pong`.
- Example: the Tits alternative for linear groups ([Wikipedia: Ping-pong lemma](https://en.wikipedia.org/wiki/Ping-pong_lemma), [Wikipedia: Tits alternative](https://en.wikipedia.org/wiki/Tits_alternative)).
- See also: T575, T666

### T575 Geometric group theory (quasi-isometry invariants)
`prove` · stage: argue · signals: group, geometry, classification
aka: Cayley graph, quasi-isometry, growth of groups, hyperbolic groups, Gromov's polynomial growth theorem, virtually nilpotent, large-scale geometry, rigidity
- What: study a group through the large-scale geometry of its Cayley graph.
- Fits when: growth, hyperbolicity or rigidity of finitely generated groups.
- Lean: — (quasi-isometry and Gromov's theorem not found in Mathlib; `GromovProduct.lean` exists).
- Example: Gromov's theorem: polynomial growth implies virtually nilpotent ([Wikipedia: Gromov's theorem](https://en.wikipedia.org/wiki/Gromov's_theorem_on_groups_of_polynomial_growth), [Wikipedia: Geometric group theory](https://en.wikipedia.org/wiki/Geometric_group_theory)).
- See also: T574, T576, T579

### T576 Actions on trees (Bass–Serre)
`prove` · stage: argue · signals: group, graph
aka: Bass–Serre theory, graphs of groups, amalgamated free products, HNN extensions, Kurosh subgroup theorem, splittings
- What: a group acting on a tree splits as an amalgam or an HNN extension.
- Fits when: subgroup structure of amalgams and free products.
- Lean: Mathlib has `HNNExtension` and `Monoid.PushoutI`; Bass–Serre theory not found.
- Example: the Kurosh subgroup theorem via Bass–Serre theory ([Wikipedia: Bass–Serre theory](https://en.wikipedia.org/wiki/Bass–Serre_theory)).
- See also: T577, T575

### T577 Covering spaces for subgroups
`prove` · stage: reformulate · signals: group, topology
aka: Galois correspondence of coverings, fundamental group, Nielsen–Schreier, Schreier index formula, subgroups of free groups, surface groups, Stallings foldings
- What: subgroups of π₁ correspond to covering spaces; topology computes their structure.
- Fits when: subgroups of free groups and surface groups.
- Lean: Mathlib: `subgroupIsFreeOfIsFree` (Nielsen–Schreier, proved with free groupoids).
- Example: Nielsen–Schreier: subgroups of free groups are free ([Wikipedia: Nielsen–Schreier theorem](https://en.wikipedia.org/wiki/Nielsen–Schreier_theorem)).
- See also: T576

### T578 Small cancellation and Dehn's algorithm
`prove` `find` · stage: argue · signals: group, construction, computation
aka: C'(1/6) condition, Greendlinger's lemma, word problem, hyperbolic groups, group presentations, prescribed properties
- What: presentations whose relators overlap little have solvable word problems and hyperbolic geometry.
- Fits when: constructing groups with prescribed properties.
- Lean: — (not found in Mathlib); a given word's reduction is a finite check.
- Example: Greendlinger's lemma and Dehn's algorithm ([Wikipedia: Small cancellation theory](https://en.wikipedia.org/wiki/Small_cancellation_theory)).
- See also: T575, T63

### T579 Property (T) and spectral gaps
`prove` `find` · stage: argue · signals: group, graph, construction, pseudorandom
aka: Kazhdan's property (T), unitary representations, spectral gap, explicit expanders, Margulis expanders, lattices in SL_n
- What: rigidity of unitary representations yields uniform expansion of Cayley graphs.
- Fits when: explicit expanders; rigidity of lattices.
- Lean: — (property (T) not found in Mathlib).
- Example: Margulis' explicit expanders ([Wikipedia: Kazhdan's property (T)](https://en.wikipedia.org/wiki/Kazhdan's_property_%28T%29), [Wikipedia: Expander graph](https://en.wikipedia.org/wiki/Expander_graph)).
- See also: T402, T575

### T580 Galois correspondence
`prove` · stage: reformulate · signals: group, polynomial, impossibility
aka: fundamental theorem of Galois theory, fixed fields, Galois group, solvability by radicals, Abel–Ruffini, constructibility
- What: translate field questions into group questions (solvability, fixed fields).
- Fits when: solvability by radicals, constructibility.
- Lean: Mathlib: `IsGalois`, `IntermediateField.fixingSubgroup` (`FieldTheory/Galois/Basic.lean`); Abel–Ruffini direction `isSolvable_gal_of_irreducible` (`FieldTheory/AbelRuffini.lean`).
- Example: the Abel–Ruffini theorem ([Wikipedia: Abel–Ruffini theorem](https://en.wikipedia.org/wiki/Abel–Ruffini_theorem)).
- See also: T581, T563

### T581 Degree counting in field towers
`prove` · stage: argue · signals: polynomial, geometry, impossibility
aka: tower law, constructible numbers, degree a power of 2, Wantzel, doubling the cube, angle trisection, straightedge and compass
- What: constructible numbers have degree a power of 2 over Q.
- Fits when: impossibility of ruler-and-compass constructions.
- Lean: Mathlib: tower law `Module.finrank_mul_finrank`, `minpoly`; constructible numbers not found as a definition.
- Example: doubling the cube and trisecting the angle are impossible (Wantzel) ([Wikipedia: Straightedge and compass construction](https://en.wikipedia.org/wiki/Straightedge_and_compass_construction)).
- See also: T580

### T582 ADE classification via positive-definite forms
`prove` · stage: argue · signals: matrix, classification
aka: Dynkin diagrams, Cartan matrix, root systems, Gabriel's theorem, quivers of finite type, simple singularities, positive-definite quadratic forms
- What: finiteness or positivity conditions force a Cartan-type form whose positive-definite cases are the ADE Dynkin diagrams.
- Fits when: classifications ending in "finitely many types" (root systems, quivers, singularities).
- Lean: Mathlib has root systems (`RootPairing`, `LinearAlgebra/RootSystem/`); a candidate form's definiteness on a small graph by `decide +kernel` on a Gram matrix.
- Example: Gabriel's theorem: quivers of finite representation type are ADE ([Wikipedia: ADE classification](https://en.wikipedia.org/wiki/ADE_classification), [Wikipedia: Gabriel's theorem](https://en.wikipedia.org/wiki/Gabriel's_theorem), [Wikipedia: Root system](https://en.wikipedia.org/wiki/Root_system)).
- See also: T411

### T583 Peirce decomposition by idempotents
`prove` · stage: argue · signals: group, matrix
aka: corner rings eRe, orthogonal idempotents, matrix units, Peirce decomposition, block decomposition of rings
- What: split a ring into corner rings eRe, eR(1−e), (1−e)Re, (1−e)R(1−e).
- Fits when: structure of rings with idempotents; spectra.
- Lean: Mathlib has `IsIdempotentElem`; no Peirce-decomposition API found.
- Example: decompositions in the Tricki article ([Tricki: Decompose your ring using idempotents](https://www.tricki.org/article/Decompose_your_ring_using_idempotents)).
- See also: T584

### T584 Localize and complete
`prove` · stage: argue · signals: integers, polynomial
aka: localization, completion, Hensel's lemma, Cohen structure theorem, local rings, p-adic completion, power series, local-to-global
- What: check a property locally, then pass to completions to work with power series.
- Fits when: commutative-algebra and arithmetic questions that are local in nature.
- Lean: Mathlib: `IsLocalization`, `AdicCompletion`, `HenselianLocalRing`.
- Example: the "localize + complete" trick of commutative algebra ([MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks), [Wikipedia: Hensel's lemma](https://en.wikipedia.org/wiki/Hensel's_lemma)).
- See also: T518, T513, T600

### T841 Vertex algebras and denominator identities
`prove` · stage: argue · signals: group, sequence, identity, symmetric
aka: vertex operator algebra, VOA, moonshine module, generalized Kac–Moody algebra, Borcherds algebra, BKM algebra, monster Lie algebra, no-ghost theorem, Goddard–Thorn, Weyl denominator formula, twisted denominator identities, McKay–Thompson series, Macdonald identities, monstrous moonshine
- What: realizes a q-series as the graded character of an algebra with a group action, builds a Lie algebra from it whose root multiplicities are the coefficients, and reads an identity off its denominator formula; twisting by group elements gives recursions that fix every coefficient from a few.
- Fits when: numbers in a q-series match dimensions of representations (a moonshine-type coincidence), or an infinite product identity looks like the denominator formula of some root system.
- Lean: Mathlib has bare vertex operators (`VertexOperator`), the Serre construction from a Cartan matrix (`Matrix.ToLieAlgebra`) and loop algebras, but no vertex algebras or denominator formulas; the final "check the first terms" step is a finite coefficient comparison (T553).
- Example: Borcherds built the monster Lie algebra from the Frenkel–Lepowsky–Meurman moonshine module, got its root multiplicities from the no-ghost theorem, matched its denominator formula with the Koike–Norton–Zagier identity, and derived twisted identities whose recursions leave only the first seven terms of each series to check ([Wikipedia: Monstrous moonshine](https://en.wikipedia.org/wiki/Monstrous_moonshine), [Wikipedia: Generalized Kac–Moody algebra](https://en.wikipedia.org/wiki/Generalized_Kac%E2%80%93Moody_algebra)); Kac and Moody saw Macdonald's product identities, Jacobi's triple product among them, as Weyl denominator formulas of affine Kac–Moody algebras ([Wikipedia: Macdonald identities](https://en.wikipedia.org/wiki/Macdonald_identities)).
- See also: T1322, T553, T582
