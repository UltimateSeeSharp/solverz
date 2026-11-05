# Modular forms and automorphic methods
Finite checks of q-series identities, small spaces of modular forms, Hecke operators, congruences, exact formulas, trace formulas, mock modular forms, automorphy, and modular forms as extremal auxiliary functions.

### T553 Finite check of modular identities (Sturm bound)
`prove` · stage: argue · signals: sequence, congruence, identity
aka: Sturm bound, finite-coefficient checks for modular forms, q-series identities, coefficient congruences, theta-function representation counts, eta quotients
- What: two forms in M_k(Γ_0(N), χ) are equal if their coefficients agree up to ⌊k·[SL_2(ℤ):Γ_0(N)]/12⌋; identities and congruences become finitely many coefficient comparisons.
- Fits when: proving an infinite family of q-series identities or congruences by a finite computation.
- Lean: the coefficients up to the bound by `decide +kernel` or `norm_num`; the Sturm bound itself is not in Mathlib (grep found only Sturm sequences), and modularity of both sides must be proved; Mathlib has `ModularForm` and `CongruenceSubgroup.Gamma0`.
- Example: Sturm's bound, used to prove coefficient congruences and identities by checking finitely many terms ([LMFDB: Sturm bound](https://www.lmfdb.org/knowledge/show/cmf.sturm_bound)).
- See also: T554, T556, T324, T122

### T554 Finite-dimensionality of spaces of modular forms
`prove` · stage: argue · signals: sequence, identity, integers
aka: dimension formulas, small explicit bases, theta functions, Eisenstein series, representation numbers of quadratic forms, Jacobi's four-square formula, sums of squares
- What: identifies a generating function as a modular form, then compares it with a small explicit basis.
- Fits when: representation numbers of quadratic forms; partition-type identities.
- Lean: Mathlib's level-one dimension results (`CuspForm.rank_eq_one_of_weight_eq_twelve`, `ModularForm.levelOne_weight_four_rank_one`), `jacobiTheta`, `eisensteinSeriesMF`.
- Example: Jacobi's four-square formula via theta functions ([Wikipedia: Jacobi's four-square theorem](https://en.wikipedia.org/wiki/Jacobi's_four-square_theorem), [Wikipedia: Sum of squares function](https://en.wikipedia.org/wiki/Sum_of_squares_function)).
- See also: T553, T555

### T555 Hecke operators
`prove` · stage: argue · signals: sequence, integers, identity
aka: Hecke eigenforms, multiplicative coefficients, Ramanujan's τ function, Hecke algebras, coefficient recursions
- What: commuting operators whose eigenforms have multiplicative coefficients.
- Fits when: multiplicativity and recursions of coefficients.
- Lean: Mathlib defines abstract Hecke rings (`HeckeRing`, NumberTheory/HeckeRing); the operators on modular forms by hand.
- Example: Mordell's proof of multiplicativity of Ramanujan's τ ([Wikipedia: Hecke operator](https://en.wikipedia.org/wiki/Hecke_operator)).
- See also: T554, T565

### T556 Congruences via modular forms mod ℓ
`prove` · stage: argue · signals: integers, congruence, sequence
aka: Ramanujan's congruences, p(5n+4) ≡ 0 mod 5, partition congruences, modular forms mod ℓ, Ono's theorem, Ramanujan-type congruences
- What: realizes a generating function as a modular form and uses the structure of forms mod ℓ.
- Fits when: congruences of partition-type functions.
- Lean: with a Sturm-type bound the congruence reduces to finitely many coefficients (T553).
- Example: Ramanujan's congruences p(5n+4) ≡ 0 mod 5 and Ono's general results ([Wikipedia: Ramanujan's congruences](https://en.wikipedia.org/wiki/Ramanujan's_congruences)).
- See also: T553, T458

### T557 Circle method on modular forms (Rademacher)
`compute` · stage: argue · signals: sequence, analytic, exact-value
aka: Hardy–Ramanujan–Rademacher formula, exact formula for p(n), partition function asymptotics, Farey dissection, Kloosterman sums, negative weight
- What: modular transformations make the circle method exact.
- Fits when: exact formulas for coefficients of modular forms of negative weight.
- Lean: —
- Example: Hardy–Ramanujan–Rademacher formula for p(n) ([Wikipedia: Partition function](https://en.wikipedia.org/wiki/Partition_function_%28number_theory%29)).
- See also: T480, T458

### T558 Rankin–Selberg unfolding
`prove` `bound` · stage: argue · signals: analytic, arithmetic-geometry
aka: Rankin–Selberg method, unfolding, Eisenstein series, L(f × g, s), mean values of coefficient sums, analytic continuation
- What: integrates a product against an Eisenstein series and unfolds it into an L-function.
- Fits when: analytic continuation and mean values of coefficient sums.
- Lean: —
- Example: the Rankin–Selberg method for L(f × g, s) ([Wikipedia: Rankin–Selberg method](https://en.wikipedia.org/wiki/Rankin–Selberg_method)).
- See also: T559, T492

### T559 Trace formulas (Selberg, Kuznetsov)
`prove` `bound` · stage: argue · signals: analytic, group
aka: Selberg trace formula, Kuznetsov formula, spectral versus geometric side, sums of Kloosterman sums, orbital integrals, Maass forms
- What: equates spectral data with geometric (orbital or Kloosterman) data.
- Fits when: averaged spectral statistics or sums of Kloosterman sums.
- Lean: —
- Example: Kuznetsov's formula behind sums of Kloosterman sums ([Wikipedia: Kuznetsov trace formula](https://en.wikipedia.org/wiki/Kuznetsov_trace_formula), [Wikipedia: Selberg trace formula](https://en.wikipedia.org/wiki/Selberg_trace_formula)).
- See also: T486, T493, T558

### T560 Mock modular completion
`prove` · stage: argue · signals: sequence, analytic
aka: mock theta functions, Zwegers, harmonic Maass forms, non-holomorphic completion, shadow, class number generating functions
- What: completes a q-series with a non-holomorphic term to restore modularity.
- Fits when: q-series that are nearly modular (Ramanujan's mock theta functions, class number generating functions).
- Lean: —
- Example: Zwegers' completion of mock theta functions ([Wikipedia: Mock modular form](https://en.wikipedia.org/wiki/Mock_modular_form)).
- See also: T554

### T561 Automorphy and functoriality
`prove` · stage: argue · signals: arithmetic-geometry, group
aka: Langlands program, potential automorphy, symmetric power L-functions, Sato–Tate conjecture, distribution of Frobenius traces
- What: proves an L-function is automorphic to gain analytic continuation and equidistribution.
- Fits when: distribution of Frobenius traces; symmetric powers.
- Lean: —
- Example: the Sato–Tate conjecture via potential automorphy ([Wikipedia: Sato–Tate conjecture](https://en.wikipedia.org/wiki/Sato–Tate_conjecture), [Wikipedia: Langlands program](https://en.wikipedia.org/wiki/Langlands_program)).
- See also: T525

### T562 Modular forms as magic auxiliary functions
`bound` `prove` · stage: construct · signals: geometry, analytic, inequality
aka: Viazovska's magic function, quasimodular forms, Fourier eigenfunctions with prescribed signs and roots, sphere packing in dimensions 8 and 24, Cohn–Elkies LP bound, E8 lattice, Leech lattice
- What: uses (quasi)modular forms to build Fourier eigenfunctions with prescribed signs and roots.
- Fits when: an LP or uncertainty bound needs an explicit extremal function.
- Lean: —
- Example: Viazovska (dim 8) and Cohn–Kumar–Miller–Radchenko–Viazovska (dim 24) sphere packing ([arXiv:1603.04246](https://arxiv.org/abs/1603.04246), [arXiv:1603.06518](https://arxiv.org/abs/1603.06518)).
- See also: T50, T629, T630
