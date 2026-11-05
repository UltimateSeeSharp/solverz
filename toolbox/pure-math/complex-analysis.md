# Complex analysis and asymptotics
Residues and contour shifts, zero counting, maximum modulus and growth, conformal and quasiconformal maps, value distribution, saddle-point asymptotics.

### T696 Residue calculus and contour shifting
`compute` `bound` · stage: argue · signals: analytic, exact-value, asymptotic
aka: residue theorem, contour integration, shifting the contour past poles, Perron's formula, Cauchy integral formula, evaluation of real integrals and series
- What: evaluate integrals and sums by residues; move contours past poles to extract main terms.
- Fits when: real integrals, series sums, Perron-formula asymptotics.
- Lean: Mathlib: Cauchy's integral formula `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`; a general residue theorem not found.
- Example: residue theorem evaluations ([Wikipedia: Residue theorem](https://en.wikipedia.org/wiki/Residue_theorem), [Tricki: shift the contour](https://www.tricki.org/article/Shift_the_contour_of_integration)).
- See also: T500, T490, T705

### T697 Argument principle and Rouché (integer-valued continuous invariants)
`prove` `compute` · stage: argue · signals: analytic, polynomial, topology
aka: argument principle, Rouché's theorem, winding number, zero counting, stability of zero counts under perturbation, fundamental theorem of algebra, Hurwitz's theorem
- What: an integer-valued quantity varying continuously is constant, so zero counts survive perturbation.
- Fits when: counting zeros; proving existence of zeros.
- Lean: Mathlib: `Complex.exists_root` (fundamental theorem of algebra); Rouché and the argument principle not found.
- Example: the fundamental theorem of algebra via Rouché ([Wikipedia: Rouché's theorem](https://en.wikipedia.org/wiki/Rouché's_theorem), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T712, T701, T74

### T698 Maximum modulus and Phragmén–Lindelöf
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: maximum modulus principle, Phragmén–Lindelöf principle, Hadamard three-lines theorem, growth control on strips and sectors, convexity bounds for L-functions, interpolation of bounds
- What: bounds on the boundary propagate inside, even on unbounded domains with growth control.
- Fits when: interpolation of bounds; convexity bounds for L-functions.
- Lean: Mathlib: `Complex.norm_le_of_forall_mem_frontier_norm_le`, `PhragmenLindelof.horizontal_strip` (`Analysis/Complex/PhragmenLindelof.lean`), three lines in `Analysis/Complex/Hadamard.lean`.
- Example: Phragmén–Lindelöf on a strip or sector; the Hadamard three-lines theorem ([Wikipedia: Phragmén–Lindelöf principle](https://en.wikipedia.org/wiki/Phragmén–Lindelöf_principle), [Wikipedia: Hadamard three-lines theorem](https://en.wikipedia.org/wiki/Hadamard_three-lines_theorem)).
- See also: T635, T477, T671

### T699 Schwarz lemma and hyperbolic geometry
`prove` `bound` · stage: argue · signals: analytic, manifold, inequality
aka: Schwarz lemma, Schwarz–Pick, hyperbolic metric contraction, Ahlfors–Schwarz, distortion of holomorphic maps, rigidity
- What: holomorphic self-maps of the disk contract the hyperbolic metric.
- Fits when: rigidity and distortion of holomorphic maps.
- Lean: Mathlib: `Complex.dist_le_div_mul_dist_of_mapsTo_ball` (`Analysis/Complex/Schwarz.lean`).
- Example: Schwarz–Pick lemma ([Wikipedia: Schwarz lemma](https://en.wikipedia.org/wiki/Schwarz_lemma)).
- See also: T698, T704

### T700 Normal families (Montel)
`prove` `find` · stage: argue · signals: analytic, dynamics
aka: Montel's theorem, normal families, locally bounded families, omitting two values, Picard's theorems, Riemann mapping theorem, Fatou and Julia sets
- What: locally bounded families, or families omitting two values, are precompact.
- Fits when: existence by limits; Picard-type theorems; dynamics.
- Lean: — (Montel's theorem for holomorphic families not found in Mathlib; `Analysis/Complex/RiemannMapping.lean` has only partial results).
- Example: proofs of Picard's theorems and the Riemann mapping theorem ([Wikipedia: Montel's theorem](https://en.wikipedia.org/wiki/Montel's_theorem), [Wikipedia: Riemann mapping theorem](https://en.wikipedia.org/wiki/Riemann_mapping_theorem)).
- See also: T656, T704

### T701 Jensen's formula and zero counting
`bound` · stage: argue · signals: analytic, inequality
aka: Jensen's formula, counting zeros from growth, log|f| averages, zero density, transcendence zero estimates, Blaschke products
- What: the average of log|f| on a circle counts the zeros inside.
- Fits when: bounding numbers of zeros from growth (also in transcendence).
- Lean: Mathlib: `AnalyticOnNhd.circleAverage_log_norm` (`Analysis/Complex/JensenFormula.lean`).
- Example: Jensen's formula ([Wikipedia: Jensen's formula](https://en.wikipedia.org/wiki/Jensen's_formula)).
- See also: T702, T543, T491

### T702 Nevanlinna theory
`prove` · stage: argue · signals: analytic, arithmetic-geometry
aka: value distribution theory, first and second main theorems, characteristic function, proximity function, functions sharing values, Vojta's dictionary, Calegari–Dimitrov–Tang
- What: quantitative value distribution of meromorphic functions.
- Fits when: uniqueness of functions sharing values; arithmetic analogues (Vojta).
- Lean: Mathlib: first main theorem in `Analysis/Complex/ValueDistribution/FirstMainTheorem.lean`; the second main theorem file is a placeholder.
- Example: Nevanlinna's second main theorem, also used by Calegari–Dimitrov–Tang ([Wikipedia: Nevanlinna theory](https://en.wikipedia.org/wiki/Nevanlinna_theory), [arXiv:2109.09040](https://arxiv.org/abs/2109.09040)).
- See also: T701, T549

### T703 Loewner evolution
`prove` · stage: argue · signals: analytic, random
aka: Loewner differential equation, driving function, slit domains, univalent functions, coefficient problems, Bieberbach conjecture, de Branges, Schramm–Loewner evolution
- What: encode a growing family of slit domains by a driving function and an ODE.
- Fits when: coefficient problems for univalent functions; random planar curves (SLE).
- Lean: — (not found in Mathlib).
- Example: de Branges' proof of the Bieberbach conjecture ([Wikipedia: De Branges's theorem](https://en.wikipedia.org/wiki/De_Branges's_theorem), [Wikipedia: Loewner differential equation](https://en.wikipedia.org/wiki/Loewner_differential_equation)).
- See also: T785, T704

### T704 Quasiconformal deformation
`prove` · stage: argue · signals: analytic, dynamics
aka: quasiconformal maps, Beltrami differentials, measurable Riemann mapping theorem, Teichmüller theory, holomorphic dynamics, no wandering domains, Sullivan
- What: deform complex structures by Beltrami differentials; finite-dimensional deformation spaces bound the possibilities.
- Fits when: holomorphic dynamics; Teichmüller theory.
- Lean: — (quasiconformal maps not found in Mathlib).
- Example: Sullivan's no-wandering-domains theorem ([Wikipedia: No-wandering-domain theorem](https://en.wikipedia.org/wiki/No-wandering-domain_theorem), [Wikipedia: Quasiconformal mapping](https://en.wikipedia.org/wiki/Quasiconformal_mapping)).
- See also: T700, T832

### T705 Saddle-point (steepest descent) asymptotics
`compute` `bound` · stage: argue · signals: analytic, sequence, asymptotic
aka: method of steepest descent, saddle-point method, Laplace's method, large-parameter asymptotics, coefficient asymptotics, Stirling, Airy asymptotics, Hayman admissibility
- What: deform the contour through a saddle of the phase.
- Fits when: asymptotics of coefficients and integrals with large parameters.
- Lean: — (not found in Mathlib); Stirling's formula itself is `Stirling.stirlingSeq`.
- Example: Stirling-type and Airy asymptotics ([Wikipedia: Method of steepest descent](https://en.wikipedia.org/wiki/Method_of_steepest_descent)).
- See also: T449, T636, T450

### T706 Uniqueness from growth (Carlson)
`prove` · stage: argue · signals: analytic, sequence, identity
aka: Carlson's theorem, entire functions of exponential type, values at integers determine the function, interpolating sequences, identity from integer values
- What: an entire function of small exponential type vanishing at the integers is zero.
- Fits when: proving identities from values at integers; interpolating sequences.
- Lean: — (not found in Mathlib).
- Example: Carlson's theorem ([Wikipedia: Carlson's theorem](https://en.wikipedia.org/wiki/Carlson's_theorem)).
- See also: T644, T701
