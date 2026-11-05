# Designs, codes and finite geometry
Constructions and nonexistence proofs for designs, difference sets, Hadamard matrices, projective planes and codes: cyclic developments, multipliers, quadratic-form obstructions, recursive constructions, code bounds, MacWilliams and invariant theory.

### T437 Difference sets and cyclic constructions
`find` · stage: construct · signals: group, set-family, construction
aka: difference sets, base blocks, developing a block through a group, Singer difference sets, cyclic projective planes, symmetric designs
- What: develop a base block through a group to get a symmetric design.
- Fits when: designs, Hadamard matrices or sequences with group symmetry.
- Lean: the difference property of a given set in `ZMod n` by `decide +kernel`.
- Example: Singer difference sets give cyclic projective planes ([Wikipedia: Difference set](https://en.wikipedia.org/wiki/Difference_set)).
- See also: T438, T441, T27

### T438 Multiplier theorems and character sums for nonexistence
`prove` · stage: argue · signals: group, set-family, impossibility
aka: Hall's multiplier theorem, group-ring equations, characters of abelian groups, circulant Hadamard matrices, difference set nonexistence
- What: group-ring and character arguments force multipliers and rule out parameters.
- Fits when: deciding which difference sets or circulant matrices exist.
- Lean: —
- Example: Hall's multiplier theorem; nonexistence results for circulant Hadamard matrices ([Wikipedia: Difference set](https://en.wikipedia.org/wiki/Difference_set), [Wikipedia: Hadamard matrix](https://en.wikipedia.org/wiki/Hadamard_matrix)).
- See also: T437, T439, T748

### T439 Number-theoretic obstruction via quadratic forms
`prove` · stage: argue · signals: matrix, integers, impossibility
aka: Bruck–Ryser–Chowla theorem, Hasse–Minkowski invariants, rational equivalence of quadratic forms, symmetric designs, projective plane of order 6
- What: an incidence matrix gives a rational equivalence of quadratic forms; Hasse–Minkowski invariants must match.
- Fits when: excluding parameters of symmetric designs or planes.
- Lean: —
- Example: Bruck–Ryser–Chowla: no projective plane of order 6 ([Wikipedia: Bruck–Ryser–Chowla theorem](https://en.wikipedia.org/wiki/Bruck–Ryser–Chowla_theorem)).
- See also: T513, T410, T7

### T440 Recursive constructions
`find` · stage: construct · signals: set-family, product-structure, construction
aka: product constructions, PBD closure, pairwise balanced designs, Wilson's fundamental construction, orthogonal Latin squares, Graeco-Latin squares, Euler's 36 officers
- What: combine small designs into large ones; Wilson's fundamental construction.
- Fits when: existence for all large admissible parameters once enough small cases exist.
- Lean: each small ingredient as a witness by `decide +kernel`; the recursion as a Lean construction.
- Example: Bose–Shrikhande–Parker: orthogonal Latin squares exist for all orders except 2 and 6 ([Wikipedia: Graeco-Latin square](https://en.wikipedia.org/wiki/Graeco-Latin_square), [Wikipedia: Combinatorial design](https://en.wikipedia.org/wiki/Combinatorial_design)).
- See also: T441, T360, T446

### T441 Hadamard matrix constructions
`find` · stage: construct · signals: matrix, finite-field, construction
aka: Hadamard matrices, Sylvester doubling, Kronecker product, Paley construction, quadratic residues, Williamson arrays, Hadamard conjecture
- What: Sylvester doubling, Paley quadratic residues, Williamson arrays.
- Fits when: orthogonal ±1 matrices of given order.
- Lean: Mathlib: `Matrix.IsHadamard` with `Matrix.IsHadamard.kronecker` (Sylvester) and the `4 ∣ n` obstruction (`LinearAlgebra/Matrix/HadamardMatrix.lean`); a concrete matrix by `decide +kernel`.
- Example: Paley's constructions from finite fields ([Wikipedia: Hadamard matrix](https://en.wikipedia.org/wiki/Hadamard_matrix)).
- See also: T437, T440, T39

### T442 Codes from groups and designs from codes
`find` · stage: construct · signals: group, set-family, construction
aka: extended Golay code, Mathieu group M24, Steiner system S(5,8,24), 5-designs, codewords of fixed weight
- What: code words of fixed weight form designs; automorphism groups give exceptional designs.
- Fits when: constructing 5-designs, Steiner systems.
- Lean: the design property of an explicit block list by `decide +kernel` at small size.
- Example: the Steiner system S(5,8,24) from the extended Golay code and the Mathieu group M24 ([Wikipedia: Steiner system](https://en.wikipedia.org/wiki/Steiner_system)).
- See also: T437, T444

### T443 Sphere-packing and averaging bounds for codes
`bound` · stage: argue · signals: set-family, inequality
aka: Hamming bound, sphere-packing bound, Plotkin bound, Gilbert–Varshamov bound, error-correcting codes, minimum distance
- What: Hamming (packing), Plotkin (double counting distances), Gilbert–Varshamov (greedy/random).
- Fits when: first bounds on code size at a given distance.
- Lean: Mathlib: `hammingDist` (`InformationTheory/Hamming.lean`); the counting by `Finset` sums.
- Example: Plotkin's bound by summing pairwise distances ([Wikipedia: Plotkin bound](https://en.wikipedia.org/wiki/Plotkin_bound), [Wikipedia: Hamming bound](https://en.wikipedia.org/wiki/Hamming_bound), [Wikipedia: Gilbert–Varshamov bound](https://en.wikipedia.org/wiki/Gilbert–Varshamov_bound)).
- See also: T327, T50, T53

### T444 MacWilliams duality
`prove` `compute` · stage: argue · signals: set-family, polynomial, identity
aka: MacWilliams identity, weight enumerators, dual codes, self-dual codes, nonnegativity of dual weight counts
- What: the weight enumerator of a code determines that of its dual.
- Fits when: self-dual codes and nonexistence via nonnegativity of dual weight counts.
- Lean: —
- Example: MacWilliams identity ([Wikipedia: MacWilliams identity](https://en.wikipedia.org/wiki/MacWilliams_identity)).
- See also: T445, T50

### T445 Invariant theory of weight enumerators
`prove` `bound` · stage: argue · signals: polynomial, group, set-family
aka: Gleason's theorem, Molien series, invariant rings of finite groups, self-dual codes, minimum distance bounds
- What: weight enumerators of self-dual codes lie in a ring of invariants of a finite group (Gleason), computable by Molien series.
- Fits when: bounding minimum distance of self-dual codes.
- Lean: —
- Example: Molien's formula for the Hilbert series of an invariant ring, the engine of Gleason-type theorems ([Wikipedia: Molien series](https://en.wikipedia.org/wiki/Molien_series)).
- See also: T444, T568

### T446 Explicit resolvable constructions
`find` · stage: construct · signals: set-family, finite-field, construction
aka: resolvable designs, Kirkman triple systems, Kirkman's schoolgirl problem, Ray-Chaudhuri–Wilson, scheduling designs, parallel classes
- What: build resolutions by cyclic or finite-geometry patterns.
- Fits when: scheduling-type designs.
- Lean: an explicit resolution by `decide +kernel` at small size.
- Example: Kirkman's schoolgirl problem and Ray-Chaudhuri–Wilson's general solution ([Wikipedia: Kirkman's schoolgirl problem](https://en.wikipedia.org/wiki/Kirkman's_schoolgirl_problem)).
- See also: T440, T437
