# Ramsey theory
Monochromatic structure in colourings: iterated pigeonhole, the book algorithm, colour focusing, Hales–Jewett, density versions, Rado, ultrafilters, algebraic lower-bound colourings, parameter sets, partition calculus.

### T427 Iterated pigeonhole
`prove` `bound` · stage: argue · signals: colouring, graph, inequality
aka: Erdős–Szekeres argument, majority colour class, Ramsey's theorem, R(k) ≤ 4^k, finite Ramsey statements, upper bounds for Ramsey numbers
- What: pick a vertex, keep the majority colour class of its neighbours, repeat; pigeonhole the resulting sequence.
- Fits when: upper bounds for Ramsey numbers and finite Ramsey statements.
- Lean: each step is pigeonhole (`Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to`); a grep finds no graph Ramsey theorem in Mathlib.
- Example: Erdős–Szekeres bound R(k) ≤ 4^k, recounted by Gowers ([Wikipedia: Ramsey's theorem](https://en.wikipedia.org/wiki/Ramsey's_theorem), [Gowers: two cultures](https://www.dpmms.cam.ac.uk/~wtg10/2cultures.pdf)).
- See also: T325, T428, T5

### T428 Book algorithm
`bound` · stage: argue · signals: colouring, graph, asymptotic
aka: proof by algorithm design, red books, density steps, diagonal Ramsey, R(k) ≤ (4 − ε)^k, Campos–Griffiths–Morris–Sahasrabudhe
- What: grow a large red "book" with controlled density steps, so either a red clique or a blue clique appears faster.
- Fits when: improving exponential bases in diagonal Ramsey.
- Lean: —
- Example: Campos–Griffiths–Morris–Sahasrabudhe R(k) ≤ (4 - ε)^k ([arXiv:2303.09521](https://arxiv.org/abs/2303.09521)).
- See also: T427, T368

### T429 Colour focusing
`prove` · stage: argue · signals: colouring, additive
aka: focused progressions, van der Waerden's theorem, induction on lengths and colours, arithmetic progressions in colourings
- What: build progressions with focused endpoints in more and more colours until two coincide.
- Fits when: van der Waerden-type statements, with inductive structure on lengths and colours.
- Lean: Mathlib proves van der Waerden via Hales–Jewett (`Combinatorics.exists_mono_homothetic_copy`).
- Example: the standard proof of van der Waerden's theorem ([Wikipedia: Van der Waerden's theorem](https://en.wikipedia.org/wiki/Van_der_Waerden's_theorem)).
- See also: T430, T434, T825

### T430 Hales–Jewett abstraction
`prove` · stage: argue · signals: colouring, product-structure
aka: Hales–Jewett theorem, combinatorial lines, words over an alphabet, Shelah's proof, van der Waerden as a corollary, projection
- What: prove the combinatorial-line theorem for words; arithmetic statements follow by projection.
- Fits when: several Ramsey statements share a "line" structure.
- Lean: Mathlib: `Combinatorics.Line.exists_mono_in_high_dimension`, `Combinatorics.exists_mono_homothetic_copy` (`Combinatorics/HalesJewett.lean`).
- Example: Shelah's primitive-recursive proof of Hales–Jewett; van der Waerden as a corollary ([Wikipedia: Hales–Jewett theorem](https://en.wikipedia.org/wiki/Hales–Jewett_theorem)).
- See also: T429, T431, T435

### T431 Density versions
`prove` · stage: argue · signals: colouring, dense, additive
aka: density Hales–Jewett theorem, Polymath, colourings to dense sets, ergodic proofs, Szemerédi's theorem
- What: replace colourings by dense sets; prove by density increment or ergodic theory.
- Fits when: a colouring theorem has a density analogue.
- Lean: —
- Example: Polymath's elementary proof of the density Hales–Jewett theorem ([arXiv:0910.3926](https://arxiv.org/abs/0910.3926)).
- See also: T430, T412, T823

### T432 Rado's columns condition
`prove` · stage: argue · signals: colouring, matrix, classification
aka: Rado's theorem, partition regularity, linear systems, Schur's theorem, monochromatic solutions
- What: a linear system is partition regular iff its matrix satisfies the columns condition.
- Fits when: deciding which equations are monochromatically solvable in every finite colouring.
- Lean: the columns condition for a given matrix is a finite check by `decide +kernel`; a grep finds no Rado or Schur theorem in Mathlib.
- Example: Rado's theorem generalizing Schur's theorem ([Wikipedia: Rado's theorem](https://en.wikipedia.org/wiki/Rado's_theorem_%28Ramsey_theory%29), [Wikipedia: Schur's theorem](https://en.wikipedia.org/wiki/Schur's_theorem)).
- See also: T429, T433

### T433 Idempotent ultrafilters
`prove` · stage: argue · signals: colouring, logic, additive
aka: Stone–Čech compactification βN, IP-sets, Hindman's finite sums theorem, finite products
- What: an idempotent ultrafilter in βN makes every member contain an IP-set.
- Fits when: infinitary Ramsey results about finite sums or products.
- Lean: Mathlib proves Hindman's theorem with idempotent ultrafilters (`Hindman.FP_partition_regular`, `Hindman.exists_idempotent_ultrafilter_le_FP`, `Combinatorics/Hindman.lean`).
- Example: Hindman's finite sums theorem via idempotent ultrafilters ([Wikipedia: Hindman's theorem](https://en.wikipedia.org/wiki/Hindman's_theorem), [Tricki: How to use ultrafilters](https://www.tricki.org/article/How_to_use_ultrafilters)).
- See also: T774, T825, T432

### T434 Explicit algebraic colourings for lower bounds
`find` `bound` · stage: construct · signals: colouring, finite-field, construction
aka: algebraic colourings, finite-field colourings, quadratic residue colourings, van der Waerden numbers, Berlekamp's bound
- What: colour by an algebraic rule (finite fields, quadratic residues) to avoid long monochromatic structures.
- Fits when: lower bounds where random colourings lose a factor.
- Lean: the colouring as a witness checked by `decide +kernel` (T118) for small parameters.
- Example: Berlekamp's finite-field lower bound W(2, p+1) > p·2^p for van der Waerden numbers ([Wikipedia: Van der Waerden number](https://en.wikipedia.org/wiki/Van_der_Waerden_number)).
- See also: T366, T388, T91

### T435 Graham–Rothschild parameter sets
`prove` · stage: argue · signals: colouring, product-structure
aka: Graham–Rothschild theorem, k-parameter subspaces, structural Ramsey theory, parameter words
- What: Ramsey theorems for k-parameter subspaces of words.
- Fits when: structural Ramsey statements about subspaces.
- Lean: Mathlib has subspaces of words (`Combinatorics.Subspace`, `Combinatorics/HalesJewett.lean`) with `Combinatorics.Subspace.exists_mono_in_high_dimension`.
- Example: the Graham–Rothschild theorem ([Wikipedia: Graham–Rothschild theorem](https://en.wikipedia.org/wiki/Graham–Rothschild_theorem)).
- See also: T430

### T436 Partition calculus
`prove` · stage: argue · signals: colouring, logic
aka: Erdős–Rado theorem, arrow notation, end-homogeneous sets, canonical Ramsey theorem, pressing-down arguments, Fodor's lemma, stationary sets, Δ-systems in uncountable combinatorics
- What: transfinite and canonical Ramsey statements via end-homogeneous sets and cardinal arithmetic; Fodor's pressing-down lemma and Δ-systems for uncountable families.
- Fits when: infinite or canonical colourings; stationary sets, uncountable families.
- Lean: Mathlib has cardinals and club and stationary sets (`IsClub`, `SetTheory/Cardinal/Cofinality/Club.lean`); a grep finds no Erdős–Rado or Fodor theorem.
- Example: the Erdős–Rado theorem (2^κ)^+ → (κ^+)²_κ ([Wikipedia: Erdős–Rado theorem](https://en.wikipedia.org/wiki/Erdős–Rado_theorem)); Fodor's lemma ([Wikipedia: Fodor's lemma](https://en.wikipedia.org/wiki/Fodor's_lemma)).
- See also: T370, T763, T767
