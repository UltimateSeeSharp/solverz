# Topological methods
Fixed-point, degree and equivariant arguments for combinatorics and analysis, obstruction theory, combinatorial topology, and the invariants of low- and high-dimensional topology.

### T707 Brouwer fixed point
`prove` · stage: argue · signals: topology, analytic, game
aka: Brouwer fixed-point theorem, Hex theorem, equilibria, continuous self-maps of a ball, existence of solutions
- What: a continuous self-map of a ball has a fixed point.
- Fits when: existence of equilibria or solutions of continuous systems.
- Lean: Mathlib has no Brouwer fixed-point theorem (grep: "Brouwer" there names Heyting algebras); a discrete version goes through Sperner (T708).
- Example: Hex cannot end in a draw (equivalent to Brouwer) ([Wikipedia: Brouwer fixed-point theorem](https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem), [Wikipedia: Hex](https://en.wikipedia.org/wiki/Hex_%28board_game%29)).
- See also: T708, T662, T712

### T708 Sperner's lemma
`prove` `find` · stage: argue · signals: topology, colouring, geometry, parity
aka: combinatorial Brouwer, Sperner labelling, fully labelled simplex, envy-free cake cutting, rental harmony, fair division, Monsky's theorem
- What: a Sperner-labelled triangulation has a fully labelled cell (in fact an odd number).
- Fits when: discrete fixed-point and fair-division problems.
- Lean: a given labelled triangulation is finite data, checked by `decide +kernel`; the lemma itself is not in Mathlib (Mathlib's "Sperner" is the antichain theorem).
- Example: envy-free cake cutting; Monsky's theorem uses it with 2-adic colouring ([Wikipedia: Sperner's lemma](https://en.wikipedia.org/wiki/Sperner's_lemma), [Wikipedia: Monsky's theorem](https://en.wikipedia.org/wiki/Monsky's_theorem)).
- See also: T707, T710, T745

### T709 Borsuk–Ulam and equivariant maps
`prove` · stage: argue · signals: topology, colouring, graph, symmetric
aka: Borsuk–Ulam theorem, Z₂-maps, antipodal maps, ham sandwich theorem, necklace splitting, Kneser's conjecture, Lovász's topological lower bound, chromatic number of Kneser graphs
- What: there is no Z₂-map S^n → S^{n−1}; antipodal symmetry forces coincidences.
- Fits when: fair division, splitting, chromatic number lower bounds.
- Lean: —
- Example: ham sandwich theorem; necklace splitting; Lovász's proof of Kneser's conjecture ([Wikipedia: Borsuk–Ulam theorem](https://en.wikipedia.org/wiki/Borsuk–Ulam_theorem), [Wikipedia: Necklace splitting problem](https://en.wikipedia.org/wiki/Necklace_splitting_problem), [Wikipedia: Kneser graph](https://en.wikipedia.org/wiki/Kneser_graph)).
- See also: T710, T711, T734

### T710 Tucker's lemma
`prove` · stage: argue · signals: topology, colouring, symmetric
aka: combinatorial Borsuk–Ulam, complementary edge, antipodal labelling, Ky Fan's lemma, combinatorial proof of Kneser's conjecture
- What: a triangulation of the n-ball, antipodally symmetric on the boundary and labelled from {±1, …, ±n} antipodally there, has a complementary edge (labels i and −i).
- Fits when: you want a constructive or finite version of a Borsuk–Ulam argument.
- Lean: one labelled triangulation is finite data, checked by `decide +kernel`; the lemma is not in Mathlib.
- Example: Matoušek's combinatorial proof of Kneser's conjecture via Tucker's lemma (Combinatorica 24 (2004) 163–170, [doi:10.1007/s00493-004-0011-1](https://doi.org/10.1007/s00493-004-0011-1)); the statement ([Wikipedia: Tucker's lemma](https://en.wikipedia.org/wiki/Tucker's_lemma)).
- See also: T709, T708

### T711 Configuration space / test map scheme
`prove` · stage: reformulate · signals: topology, geometry, symmetric, impossibility
aka: CS/TM scheme, equivariant obstruction, topological Tverberg, embedding problems, van Kampen–Flores, Özaydin, constraint method
- What: turns a geometric problem into nonexistence of an equivariant map; obstruction theory decides.
- Fits when: Tverberg-type and embedding problems.
- Lean: —
- Example: topological Tverberg for prime powers; its failure for other n (Frick, Mabillard–Wagner) ([Wikipedia: Tverberg's theorem](https://en.wikipedia.org/wiki/Tverberg's_theorem), [arXiv:1502.00947](https://arxiv.org/abs/1502.00947), [arXiv:1508.02349](https://arxiv.org/abs/1508.02349)).
- See also: T709, T721, T736

### T712 Degree and winding number
`prove` · stage: argue · signals: topology, analytic, polynomial
aka: Brouwer degree, mapping degree, winding number, index of a zero, fundamental theorem of algebra, zeros of vector fields
- What: an integer-valued homotopy invariant of maps; nonzero degree forces surjectivity or zeros.
- Fits when: existence of zeros of vector fields or polynomials.
- Lean: Mathlib: `AddCircle.windingNumber` (fundamental group of the circle is ℤ), `Complex.exists_root` (fundamental theorem of algebra).
- Example: topological proof of the fundamental theorem of algebra ([Wikipedia: Degree of a continuous mapping](https://en.wikipedia.org/wiki/Degree_of_a_continuous_mapping), [Wikipedia: Fundamental theorem of algebra](https://en.wikipedia.org/wiki/Fundamental_theorem_of_algebra)).
- See also: T697, T715, T707

### T713 Intermediate-value and parity-of-intersections arguments
`prove` · stage: argue · signals: topology, geometry, parity
aka: intermediate value theorem, odd crossing count, inscribed square problem, inscribed rectangles, Toeplitz conjecture, equipartitions, mod 2 intersection number
- What: a continuous family crosses an obstacle an odd number of times.
- Fits when: inscribed shapes, equipartitions.
- Lean: Mathlib: `intermediate_value_Icc`.
- Example: inscribed rectangles and squares in Jordan curves (smooth cases, Greene–Lobb) ([Wikipedia: Inscribed square problem](https://en.wikipedia.org/wiki/Inscribed_square_problem)).
- See also: T712, T332

### T714 Euler characteristic counting
`prove` `bound` · stage: argue · signals: graph, geometry, topology, sparse
aka: Euler's formula, V − E + F = 2, planar graphs, edge bounds, Sylvester–Gallai, Melchior's inequality, small configurations
- What: V − E + F = 2 bounds the edges of planar graphs and forces small configurations.
- Fits when: planar structures, discharging, combinatorial geometry.
- Lean: Mathlib has no planar-graph Euler formula; it has Euler characteristics of chain complexes (Algebra/Homology/EulerCharacteristic.lean).
- Example: Melchior's proof of Sylvester–Gallai via Euler's formula ([Wikipedia: Euler characteristic](https://en.wikipedia.org/wiki/Euler_characteristic), [Wikipedia: Sylvester–Gallai theorem](https://en.wikipedia.org/wiki/Sylvester–Gallai_theorem)).
- See also: T464, T738

### T715 Poincaré–Hopf and Lefschetz fixed points
`prove` · stage: argue · signals: manifold, topology, dynamics
aka: Poincaré–Hopf index theorem, hairy ball theorem, Lefschetz number, Lefschetz fixed-point theorem, indices of zeros
- What: sums of indices of zeros or fixed points equal a topological invariant.
- Fits when: forcing zeros of vector fields or fixed points of maps.
- Lean: —
- Example: the hairy ball theorem; Lefschetz fixed-point theorem ([Wikipedia: Hairy ball theorem](https://en.wikipedia.org/wiki/Hairy_ball_theorem), [Wikipedia: Lefschetz fixed-point theorem](https://en.wikipedia.org/wiki/Lefschetz_fixed-point_theorem)).
- See also: T712, T716

### T716 Morse theory
`prove` `bound` · stage: argue · signals: manifold, topology
aka: Morse inequalities, critical points, handle decompositions, loop spaces, Bott periodicity, closed geodesics
- What: critical points of a generic function reflect the topology; topology bounds critical points.
- Fits when: counting critical points or geodesics; handle decompositions.
- Lean: —
- Example: Morse inequalities; Bott periodicity via Morse theory of loop spaces ([Wikipedia: Morse theory](https://en.wikipedia.org/wiki/Morse_theory)).
- See also: T717, T723, T718

### T717 Lusternik–Schnirelmann category
`prove` `bound` · stage: argue · signals: manifold, topology
aka: LS category, cup length, critical point lower bounds, theorem of three geodesics, closed geodesics on spheres
- What: any smooth function has at least cat(M) critical points.
- Fits when: lower bounds on numbers of critical points or closed geodesics.
- Lean: —
- Example: the theorem of three closed geodesics on spheres (Lyusternik–Schnirelmann) ([Wikipedia: Lusternik–Schnirelmann category](https://en.wikipedia.org/wiki/Lusternik–Schnirelmann_category), [Wikipedia: Theorem of the three geodesics](https://en.wikipedia.org/wiki/Theorem_of_the_three_geodesics)).
- See also: T716, T677

### T718 Floer homology
`prove` `bound` · stage: argue · signals: manifold, topology, dynamics
aka: Hamiltonian Floer homology, Lagrangian Floer homology, infinite-dimensional Morse theory, Arnold conjecture, symplectic fixed points, Heegaard Floer
- What: an infinite-dimensional Morse theory whose rank bounds fixed points or intersections.
- Fits when: symplectic fixed points, Lagrangian intersections, 3-manifold invariants.
- Lean: —
- Example: the Arnold conjecture ([Wikipedia: Arnold conjecture](https://en.wikipedia.org/wiki/Arnold_conjecture), [Wikipedia: Floer homology](https://en.wikipedia.org/wiki/Floer_homology)).
- See also: T716, T694

### T719 Characteristic classes as obstructions
`prove` · stage: argue · signals: manifold, topology, impossibility
aka: Stiefel–Whitney classes, Chern classes, Pontryagin classes, Whitney duality, nonembedding, nonimmersion, sections of bundles, projective spaces
- What: Stiefel–Whitney, Chern and Pontryagin classes must vanish, or satisfy relations, if a bundle, section or embedding exists.
- Fits when: nonembedding, nonimmersion, nonexistence of sections.
- Lean: —
- Example: Whitney's non-immersion of RP^{2^r} in R^{2^{r+1}−2} via Whitney duality (Milnor–Stasheff, Characteristic Classes, §4); the classes ([Wikipedia: Stiefel–Whitney class](https://en.wikipedia.org/wiki/Stiefel–Whitney_class)).
- See also: T720, T721

### T720 Cohomology operations and K-theory
`prove` · stage: argue · signals: topology, impossibility
aka: Steenrod squares, Steenrod algebra, Adams operations, topological K-theory, Hopf invariant one, vector fields on spheres, division algebras
- What: Steenrod squares and Adams operations give finer obstructions than cohomology rings.
- Fits when: Hopf invariant one, vector fields on spheres.
- Lean: —
- Example: Adams: Hopf invariant one only in dimensions 1, 2, 4, 8, and the maximal number of vector fields on spheres ([Wikipedia: Hopf invariant](https://en.wikipedia.org/wiki/Hopf_invariant), [Wikipedia: Vector fields on spheres](https://en.wikipedia.org/wiki/Vector_fields_on_spheres), [Wikipedia: Steenrod algebra](https://en.wikipedia.org/wiki/Steenrod_algebra)).
- See also: T719, T732

### T721 Obstruction theory
`prove` · stage: argue · signals: topology, impossibility
aka: the obstruction lives in a group, show the group is zero, extension problems, cohomology with local coefficients, trivial cohomology box, lifting problems
- What: solves extension problems skeleton by skeleton, with each obstruction a cohomology class.
- Fits when: existence of maps, sections, structures.
- Lean: —
- Example: classical obstruction theory; the "trivial cohomology box" trick on MO ([Wikipedia: Obstruction theory](https://en.wikipedia.org/wiki/Obstruction_theory), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T711, T719, T604

### T722 Nerve lemma
`prove` · stage: argue · signals: topology, geometry, set-family
aka: nerve theorem, good covers, Čech nerve, topological Helly, connectivity of complexes, Leray's theorem
- What: the nerve of a good cover has the homotopy type of the union.
- Fits when: topological Helly theorems, connectivity of complexes from combinatorics.
- Lean: —
- Example: the nerve theorem: a good cover's union is homotopy equivalent to its nerve ([Wikipedia: Nerve complex](https://en.wikipedia.org/wiki/Nerve_complex)).
- See also: T735, T723

### T723 Discrete Morse theory
`prove` `compute` · stage: argue · signals: topology, graph, order
aka: Forman's discrete Morse theory, acyclic matchings, collapses, critical cells, graph complexes, independence complexes, order complexes of posets
- What: an acyclic matching collapses a complex to few critical cells.
- Fits when: homotopy types of complexes from graphs and posets.
- Lean: one acyclic matching on a finite complex is finite data, checked by `decide +kernel`.
- Example: Forman's discrete Morse theory applied to graph complexes ([Wikipedia: Discrete Morse theory](https://en.wikipedia.org/wiki/Discrete_Morse_theory)).
- See also: T716, T722, T73

### T724 Van Kampen and Mayer–Vietoris
`compute` `prove` · stage: argue · signals: topology, group
aka: Seifert–van Kampen theorem, Mayer–Vietoris sequence, gluing, fundamental groups of unions, homology of unions, amalgamated free products
- What: computes invariants of a union from the pieces and their intersection.
- Fits when: fundamental groups and homology of glued spaces.
- Lean: Mathlib has `FundamentalGroup` and singular homology (AlgebraicTopology/SingularHomology); Seifert–van Kampen is not there.
- Example: Seifert–van Kampen theorem ([Wikipedia: Seifert–van Kampen theorem](https://en.wikipedia.org/wiki/Seifert–van_Kampen_theorem), [Wikipedia: Mayer–Vietoris sequence](https://en.wikipedia.org/wiki/Mayer–Vietoris_sequence)).
- See also: T576, T577, T597

### T725 Homology for point-set theorems
`prove` · stage: argue · signals: topology
aka: invariance of domain, Jordan curve theorem, Jordan–Brouwer separation, degree arguments for open sets, curves in the plane
- What: degree and homology prove statements about open sets and curves.
- Fits when: invariance of domain, Jordan curve-type statements.
- Lean: Mathlib has neither the Jordan curve theorem nor invariance of domain (grep).
- Example: invariance of domain; Jordan curve theorem ([Wikipedia: Invariance of domain](https://en.wikipedia.org/wiki/Invariance_of_domain), [Wikipedia: Jordan curve theorem](https://en.wikipedia.org/wiki/Jordan_curve_theorem)).
- See also: T712, T724

### T726 Knot homologies and concordance invariants
`prove` `bound` · stage: argue · signals: topology
aka: Khovanov homology, Rasmussen s-invariant, knot Floer homology, slice genus, unknotting number, sliceness, Milnor conjecture, Conway knot
- What: categorified invariants give genus and sliceness bounds.
- Fits when: slice genus, unknotting number, sliceness of specific knots.
- Lean: —
- Example: Rasmussen's combinatorial proof of the Milnor conjecture from Khovanov homology; Piccirillo's proof that the Conway knot is not slice ([Wikipedia: Khovanov homology](https://en.wikipedia.org/wiki/Khovanov_homology), [Wikipedia: Milnor conjecture](https://en.wikipedia.org/wiki/Milnor_conjecture_%28topology%29), [arXiv:1808.02923](https://arxiv.org/abs/1808.02923)).
- See also: T727, T601

### T727 Trace / knot-trace swap
`prove` · stage: reformulate · signals: topology
aka: 0-trace, knot traces, Kirby calculus, trace diffeomorphism, Conway knot, sliceness when direct invariants vanish
- What: replaces a knot by another with the same 0-trace whose invariants are computable.
- Fits when: sliceness questions where direct invariants vanish.
- Lean: —
- Example: Piccirillo's Conway knot argument via a Kirby-calculus trace diffeomorphism ([arXiv:1808.02923](https://arxiv.org/abs/1808.02923), [Wikipedia: Kirby calculus](https://en.wikipedia.org/wiki/Kirby_calculus)).
- See also: T726

### T728 Normal surface theory
`prove` `compute` · stage: argue · signals: topology, computation
aka: normal forms with bounded search, Haken's algorithm, unknot recognition, normal surfaces, fundamental surfaces, bounded-complexity witnesses, 3-manifold algorithms, Smith normal form, canonical game forms
- What: essential surfaces can be put in normal form, so a witness, if any, has bounded complexity and a finite linear-algebra search finds it.
- Fits when: algorithmic 3-manifold questions with finite certificates; existence problems with a structure theorem bounding witnesses.
- Lean: a found normal surface is a vector of integers satisfying matching equations, checked by `decide +kernel`; the bounding theorem needs a Lean proof.
- Example: Haken's algorithm for recognizing the unknot ([Wikipedia: Normal surface](https://en.wikipedia.org/wiki/Normal_surface), [Wikipedia: Unknotting problem](https://en.wikipedia.org/wiki/Unknotting_problem)).
- See also: T410, T814, T118

### T729 Gauge theory
`prove` · stage: argue · signals: manifold, topology, pde
aka: instantons, Yang–Mills, Seiberg–Witten monopoles, Donaldson invariants, smooth 4-manifolds, exotic structures
- What: moduli spaces of instantons or monopoles yield invariants of smooth 4-manifolds.
- Fits when: smooth versus topological 4-manifold questions.
- Lean: —
- Example: Donaldson's diagonalization theorem ([Wikipedia: Donaldson's theorem](https://en.wikipedia.org/wiki/Donaldson's_theorem)).
- See also: T718, T693

### T730 Surgery and the Whitney trick
`prove` · stage: argue · signals: manifold, topology, classification
aka: h-cobordism theorem, Whitney trick, surgery theory, high-dimensional Poincaré conjecture, handle cancellation, manifold classification
- What: cancels intersections in dimension ≥ 5 to classify manifolds.
- Fits when: high-dimensional manifold classification.
- Lean: —
- Example: Smale's h-cobordism theorem and the high-dimensional Poincaré conjecture ([Wikipedia: H-cobordism](https://en.wikipedia.org/wiki/H-cobordism), [Wikipedia: Whitney embedding theorem](https://en.wikipedia.org/wiki/Whitney_embedding_theorem)).
- See also: T729

### T731 Rigidity of hyperbolic structures
`prove` · stage: argue · signals: manifold, topology, group
aka: Mostow rigidity, geometrization, hyperbolic 3-manifolds, hyperbolic volume, lattices in Lie groups
- What: geometric structures are determined by topology, so geometric invariants become topological.
- Fits when: 3-manifolds and lattices; invariants like volume.
- Lean: —
- Example: Mostow rigidity; Thurston's geometrization ([Wikipedia: Mostow rigidity theorem](https://en.wikipedia.org/wiki/Mostow_rigidity_theorem), [Wikipedia: Geometrization conjecture](https://en.wikipedia.org/wiki/Geometrization_conjecture)).
- See also: T575, T686

### T732 Spectral sequence computations in stable homotopy
`compute` `prove` · stage: argue · signals: topology, exact-value
aka: Adams spectral sequence, stable stems, Kervaire invariant problem, machine-scale bookkeeping, Ext over the Steenrod algebra
- What: computes homotopy groups by Adams-type spectral sequences, now with machine-scale bookkeeping.
- Fits when: Kervaire invariant, stable stems.
- Lean: —
- Example: Lin–Wang–Xu settle the last Kervaire invariant problem in dimension 126 ([arXiv:2412.10879](https://arxiv.org/abs/2412.10879)).
- See also: T597, T720

### T733 Algebraic K-theory and trace methods as detectors
`prove` · stage: argue · signals: topology, impossibility
aka: algebraic K-theory, trace methods, chromatic homotopy theory, telescope conjecture, localizations
- What: shows a localization is not what it should be by computing its K-theory.
- Fits when: chromatic homotopy theory conjectures.
- Lean: —
- Example: Burklund–Hahn–Levy–Schlank's counterexamples to the telescope conjecture ([arXiv:2310.17459](https://arxiv.org/abs/2310.17459)).
- See also: T732

### T734 Equivariant topology
`prove` · stage: argue · signals: topology, group, symmetric
aka: group actions on spaces, Borel cohomology, orbit spaces, fixed-point sets, Smith theory, equivariant maps
- What: studies spaces with group actions through their orbit structure and Borel cohomology.
- Fits when: symmetric configurations, fixed-point sets.
- Lean: —
- Example: equivariant methods in combinatorial topology ([Wikipedia: Equivariant topology](https://en.wikipedia.org/wiki/Equivariant_topology)).
- See also: T709, T711

### T837 Knot polynomials from state sums
`prove` `bound` · stage: argue · signals: topology, polynomial, inequality
aka: Jones polynomial, Kauffman bracket, skein relation, smoothings, span, breadth, crossing number, alternating knots, Tait conjectures, von Neumann algebras, braid group representations, Potts model
- What: a polynomial invariant computed from any diagram (Kauffman's bracket by a skein rule at each crossing, or Jones's trace of a braid representation); its span (breadth) bounds the crossing number from below and gives it exactly for reduced alternating diagrams.
- Fits when: a minimality, crossing-number or non-equivalence claim about knot or link diagrams; compute the invariant of one diagram and compare its span or value with what the claim needs.
- Lean: Mathlib has no knot theory (only quandles); the bracket of a given n-crossing diagram expands into 2^n smoothings, an exact `LaurentPolynomial ℤ` computation, but invariance under Reidemeister moves must be formalized before the value counts.
- Example: Jones found the polynomial in operator algebras, as a trace of a braid representation into an algebra known from the Potts model ([Wikipedia: Jones polynomial](https://en.wikipedia.org/wiki/Jones_polynomial)); Kauffman, Murasugi and Thistlethwaite used it in 1987 to prove that reduced alternating diagrams have the fewest crossings ([Wikipedia: Tait conjectures](https://en.wikipedia.org/wiki/Tait_conjectures)); the breadth gives the crossing number of alternating links directly ([arXiv:1510.01622](https://arxiv.org/abs/1510.01622)).
- See also: T726, T728
