# Homological and categorical methods
Spectral sequences, representability, derived functors, sheaf and group cohomology as obstructions, categorification, representation and homological stability.

### T597 Spectral sequences and towers
`compute` `prove` · stage: argue · signals: topology, group, exact-value
aka: Serre spectral sequence, filtered complexes, Leray spectral sequence, Postnikov towers, iterated extensions, pages and differentials, homology of fibrations
- What: compute a hard invariant through a filtered sequence of easier approximations.
- Fits when: homology of fibrations, filtered complexes, iterated extensions.
- Lean: Mathlib defines spectral sequences (`Algebra/Homology/SpectralSequence/Basic.lean`); the classical ones (Serre) not found.
- Example: Serre spectral sequence computations of homotopy groups ([Wikipedia: Spectral sequence](https://en.wikipedia.org/wiki/Spectral_sequence), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T599, T732, T724

### T598 Yoneda and representability
`prove` · stage: argue · signals: identity
aka: Yoneda lemma, representable functors, universal properties, moduli spaces, universal objects, natural isomorphisms, functor of points
- What: identify an object by the functor it represents; constructions become obvious on the functor side.
- Fits when: constructing moduli or universal objects; proving isomorphisms naturally.
- Lean: Mathlib: `CategoryTheory.yoneda`, `CategoryTheory.yonedaEquiv`, `CategoryTheory.yonedaLemma`.
- Example: the Yoneda lemma ([Wikipedia: Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma)).
- See also: T319

### T599 Derived functors and resolutions (Tor, Ext)
`prove` `compute` · stage: argue · signals: polynomial, exact-value
aka: free and projective resolutions, Tor, Ext, Betti numbers, intersection multiplicity, Serre's multiplicity conjectures, failure of exactness, homological algebra
- What: replace a module by a free resolution; Tor and Ext measure the failure of exactness and become computable invariants.
- Fits when: intersection multiplicities, Betti numbers, obstructions that a naive tensor product loses.
- Lean: Mathlib: `CategoryTheory.Abelian.Ext`, `CategoryTheory.Tor` (`CategoryTheory/Monoidal/Tor.lean`), derived-category `Ext`.
- Example: Serre defined intersection multiplicity through Tor, leading to his multiplicity conjectures ([Wikipedia: Serre's multiplicity conjectures](https://en.wikipedia.org/wiki/Serre%27s_multiplicity_conjectures), [Wikipedia: Tor functor](https://en.wikipedia.org/wiki/Tor_functor)).
- See also: T597, T604, T588

### T600 Sheaf cohomology as the local-to-global obstruction
`prove` · stage: argue · signals: topology, impossibility, local-constraints
aka: sheaves, Čech cohomology, gluing, obstruction class, contextuality, non-locality, Kochen–Specker configurations, solvable on every patch but not globally
- What: local solutions glue to a global one exactly when a cohomology class vanishes.
- Fits when: a problem is solvable on every patch (every context, every chart) but not obviously globally.
- Lean: Mathlib: sheaf cohomology on sites (`CategoryTheory/Sites/SheafCohomology/`, with Čech and Mayer–Vietoris files).
- Example: Abramsky–Brandenburger treat non-locality and contextuality, including Kochen–Specker configurations, as sheaf obstructions ([arXiv:1102.0264](https://arxiv.org/abs/1102.0264), [Wikipedia: Sheaf cohomology](https://en.wikipedia.org/wiki/Sheaf_cohomology)).
- See also: T721, T513, T604

### T601 Positivity by categorification
`prove` · stage: argue · signals: polynomial, inequality
aka: categorification, graded dimensions, Soergel bimodules, Kazhdan–Lusztig positivity, Hodge theory for Soergel bimodules, combinatorial interpretation of coefficients
- What: show integers or polynomial coefficients are dimensions or graded ranks of objects; positivity then comes free.
- Fits when: a coefficient sequence is conjectured nonnegative and no combinatorial interpretation is known.
- Lean: —
- Example: Elias–Williamson proved Kazhdan–Lusztig positivity for all Coxeter systems via Soergel bimodules ([arXiv:1212.0791](https://arxiv.org/abs/1212.0791), [Wikipedia: Categorification](https://en.wikipedia.org/wiki/Categorification)).
- See also: T406, T405, T336

### T602 Representation stability (FI-modules)
`prove` `compute` · stage: argue · signals: group, sequence, regular-structure
aka: FI-modules, representation stability, eventually polynomial characters, configuration spaces, diagonal coinvariant algebras, S_n-representations indexed by n
- What: a sequence of S_n-representations that forms a finitely generated FI-module has eventually polynomial characters and dimensions.
- Fits when: counts or Betti numbers indexed by n look eventually polynomial (configuration spaces, coinvariants).
- Lean: — (FI-modules not found in Mathlib).
- Example: Church–Ellenberg–Farb on configuration spaces and diagonal coinvariant algebras ([arXiv:1204.4533](https://arxiv.org/abs/1204.4533)).
- See also: T603, T570

### T603 Homological stability, then point counting
`prove` · stage: argue · signals: arithmetic-geometry, finite-field, topology, asymptotic
aka: homological stability, Grothendieck–Lefschetz trace formula, Hurwitz spaces, Cohen–Lenstra heuristics over function fields, arithmetic statistics over F_q(t), moduli spaces
- What: show the homology of a family of moduli spaces stabilizes, then turn it into point counts over F_q by the Grothendieck–Lefschetz trace formula.
- Fits when: arithmetic statistics over function fields.
- Lean: —
- Example: Ellenberg–Venkatesh–Westerland's Cohen–Lenstra theorem over F_q(t) via Hurwitz spaces ([arXiv:0912.0325](https://arxiv.org/abs/0912.0325)).
- See also: T602, T596

### T604 Group cohomology for extensions and lifting obstructions
`prove` `compute` · stage: argue · signals: group, impossibility, classification
aka: H²(G, M), central extensions, Schur multiplier, Hopf's formula, cocycles, lifting obstructions, extending representations, projective representations
- What: H² classifies central extensions; obstructions to lifting or extending live in computable cohomology groups.
- Fits when: does a group, representation or cocycle extend; Schur multipliers.
- Lean: Mathlib: `groupCohomology`, `groupCohomology.H2` (`RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`), `GroupExtension`.
- Example: H²(G, M) and central extensions; Hopf's formula for the Schur multiplier ([Wikipedia: Group cohomology](https://en.wikipedia.org/wiki/Group_cohomology)).
- See also: T721, T566, T29
