# Dynamics and ergodic theory
Ergodic Ramsey theory, structure and rigidity of measure-preserving actions, recurrence, symbolic coding and shadowing, KAM, renormalization, transfer operators, and topological arguments for one- and two-dimensional dynamics.

### T823 Furstenberg correspondence principle
`prove` · stage: reformulate · signals: dynamics, additive, integers, dense
aka: ergodic Ramsey theory, multiple recurrence, Szemerédi's theorem, polynomial Szemerédi, Bergelson–Leibman, density Ramsey theorems
- What: a dense set of integers yields a measure-preserving system; recurrence there gives patterns in the set.
- Fits when: density Ramsey theorems.
- Lean: —
- Example: Furstenberg's ergodic proof of Szemerédi's theorem; polynomial extensions ([Wikipedia: Ergodic Ramsey theory](https://en.wikipedia.org/wiki/Ergodic_Ramsey_theory), [Wikipedia: Szemerédi's theorem](https://en.wikipedia.org/wiki/Szemerédi's_theorem)).
- See also: T824, T431, T414

### T824 Structure theory of measure-preserving systems
`prove` · stage: argue · signals: dynamics, additive, group
aka: Furstenberg–Zimmer structure theorem, compact and weak-mixing parts, characteristic factors, Host–Kra factors, nilsystems, nilmanifolds, multiple ergodic averages
- What: decomposes a system into compact and weak-mixing parts; characteristic factors are nilsystems.
- Fits when: multiple ergodic averages; higher-order Fourier analysis.
- Lean: —
- Example: Host–Kra nilsystems behind the Green–Tao–Ziegler inverse theorem ([arXiv:1009.3998](https://arxiv.org/abs/1009.3998), [Wikipedia: Nilmanifold](https://en.wikipedia.org/wiki/Nilmanifold)).
- See also: T823, T414, T413

### T825 Topological dynamics for colourings
`prove` · stage: reformulate · signals: dynamics, colouring, additive
aka: Furstenberg–Weiss, shift spaces, minimal systems, uniform recurrence, multiple Birkhoff recurrence, van der Waerden's theorem, colouring Ramsey theorems
- What: colourings become points of a compact shift space; minimal systems and recurrence give monochromatic patterns.
- Fits when: colouring (not density) Ramsey theorems.
- Lean: van der Waerden follows from Mathlib's Hales–Jewett (`Combinatorics.exists_mono_homothetic_copy`); the dynamical proof is not there.
- Example: Furstenberg–Weiss dynamical proof of van der Waerden's theorem ([Wikipedia: Van der Waerden's theorem](https://en.wikipedia.org/wiki/Van_der_Waerden's_theorem), [Wikipedia: Ergodic Ramsey theory](https://en.wikipedia.org/wiki/Ergodic_Ramsey_theory)).
- See also: T430, T823, T433

### T826 Unipotent flows (Ratner)
`prove` · stage: argue · signals: dynamics, group, integers
aka: Ratner's theorems, orbit closures, invariant measures, homogeneous spaces, Oppenheim conjecture, values of quadratic forms, Margulis
- What: orbit closures and invariant measures of unipotent flows are algebraic.
- Fits when: values of quadratic forms, counting in homogeneous spaces.
- Lean: —
- Example: Margulis' proof of the Oppenheim conjecture ([Wikipedia: Ratner's theorems](https://en.wikipedia.org/wiki/Ratner's_theorems), [Wikipedia: Oppenheim conjecture](https://en.wikipedia.org/wiki/Oppenheim_conjecture)).
- See also: T827, T482

### T827 Measure rigidity for higher-rank actions
`prove` · stage: argue · signals: dynamics, integers, group
aka: Einsiedler–Katok–Lindenstrauss, positive entropy, diagonal actions, Littlewood conjecture, multiplicative Diophantine approximation
- What: invariant measures with positive entropy are algebraic.
- Fits when: Diophantine problems with multiplicative structure.
- Lean: —
- Example: Einsiedler–Katok–Lindenstrauss: exceptions to Littlewood's conjecture have dimension zero ([arXiv:math/0612721](https://arxiv.org/abs/math/0612721), [Wikipedia: Littlewood conjecture](https://en.wikipedia.org/wiki/Littlewood_conjecture)).
- See also: T826, T545

### T828 Poincaré recurrence and ergodic theorems
`prove` · stage: argue · signals: dynamics, random
aka: Poincaré recurrence theorem, Birkhoff's ergodic theorem, von Neumann's mean ergodic theorem, time averages, space averages, return times, conservative maps
- What: almost every point returns; time averages equal space averages.
- Fits when: return-time statements, averages along orbits.
- Lean: Mathlib: `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem` (Poincaré recurrence), `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` (mean ergodic theorem).
- Example: Poincaré recurrence; Birkhoff's ergodic theorem ([Wikipedia: Poincaré recurrence theorem](https://en.wikipedia.org/wiki/Poincaré_recurrence_theorem), [Wikipedia: Ergodic theory](https://en.wikipedia.org/wiki/Ergodic_theory)).
- See also: T823, T482

### T829 Symbolic coding (Markov partitions)
`compute` `prove` · stage: reformulate · signals: dynamics, sequence, exact-value
aka: Markov partitions, symbolic dynamics, shifts of finite type, Anosov maps, topological entropy, counting periodic orbits, transition matrices
- What: encodes a hyperbolic system as a shift of finite type.
- Fits when: counting periodic orbits, entropy computations.
- Lean: periodic-orbit counts of a shift of finite type are traces of powers of its 0-1 transition matrix, checked by `decide +kernel`.
- Example: Markov partitions for Anosov maps ([Wikipedia: Markov partition](https://en.wikipedia.org/wiki/Markov_partition), [Wikipedia: Symbolic dynamics](https://en.wikipedia.org/wiki/Symbolic_dynamics)).
- See also: T830, T833, T411

### T830 Shadowing
`prove` · stage: argue · signals: dynamics, numeric-only
aka: shadowing lemma, pseudo-orbits, hyperbolic sets, true orbits near numerical orbits
- What: pseudo-orbits of hyperbolic systems are tracked by true orbits.
- Fits when: turning approximate (numerical) orbits into real ones.
- Lean: needs interval enclosures of the pseudo-orbit (T64, T66) plus a Lean proof of the shadowing estimate.
- Example: the shadowing lemma ([Wikipedia: Shadowing lemma](https://en.wikipedia.org/wiki/Shadowing_lemma)).
- See also: T829, T64, T73

### T831 KAM (Nash–Moser-type iteration)
`prove` · stage: argue · signals: dynamics, pde, analytic
aka: Kolmogorov–Arnold–Moser theorem, Nash–Moser iteration, small divisors, quasi-periodic motion, invariant tori, rapidly converging Newton scheme
- What: a rapidly converging Newton scheme beats small divisors.
- Fits when: persistence of quasi-periodic motion under perturbation.
- Lean: —
- Example: the KAM theorem ([Wikipedia: Kolmogorov–Arnold–Moser theorem](https://en.wikipedia.org/wiki/Kolmogorov–Arnold–Moser_theorem)).
- See also: T832, T68, T1301

### T832 Renormalization
`prove` `compute` · stage: argue · signals: dynamics, regular-structure, analytic
aka: renormalization group, coarse-graining, renormalization operator, universality, self-similarity, Feigenbaum constants, period doubling, induction on scales
- What: views the object as a fixed point of a scale-change operator on a space of similar objects; universality is an attracting fixed point, whose existence is often proved with computer help.
- Fits when: universality and self-similarity; a template for induction on scales.
- Lean: the fixed-point step needs rigorous enclosures (T68) plus a Lean proof of the contraction estimate.
- Example: Feigenbaum universality (Lanford's computer-assisted proof, 1982) ([Wikipedia: Feigenbaum constants](https://en.wikipedia.org/wiki/Feigenbaum_constants), [Wikipedia: Renormalization group](https://en.wikipedia.org/wiki/Renormalization_group), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T831, T646, T68

### T833 Transfer operators and thermodynamic formalism
`bound` `prove` · stage: argue · signals: dynamics, operator, integers
aka: Ruelle transfer operator, thermodynamic formalism, pressure, Hausdorff dimension of Cantor sets, continued-fraction Cantor sets, Zaremba's conjecture, orbit counting
- What: spectral properties of transfer operators control dimension and counting.
- Fits when: continued-fraction Cantor sets, orbit counting.
- Lean: —
- Example: Bourgain–Kontorovich progress on Zaremba's conjecture ([arXiv:1107.3776](https://arxiv.org/abs/1107.3776), [Wikipedia: Transfer operator](https://en.wikipedia.org/wiki/Transfer_operator)).
- See also: T829, T538, T72

### T834 Combinatorics of periods
`prove` · stage: argue · signals: dynamics, order
aka: Sharkovskii's theorem, Sharkovskii ordering, period three implies chaos, interval maps, forced periods
- What: continuity on an interval forces an ordering of the periods that occur.
- Fits when: one-dimensional dynamics.
- Lean: —
- Example: Sharkovskii's theorem (period 3 implies all periods) ([Wikipedia: Sharkovskii's theorem](https://en.wikipedia.org/wiki/Sharkovskii's_theorem)).
- See also: T713, T835

### T835 Planar topology for flows
`prove` · stage: argue · signals: dynamics, topology
aka: Poincaré–Bendixson theorem, limit cycles, ω-limit sets, planar ODE, Jordan-curve arguments
- What: Jordan-curve arguments restrict limit sets of flows in the plane.
- Fits when: 2D ODE.
- Lean: Mathlib has ω-limit sets (Dynamics/OmegaLimit.lean); Poincaré–Bendixson is not there (grep).
- Example: Poincaré–Bendixson theorem ([Wikipedia: Poincaré–Bendixson theorem](https://en.wikipedia.org/wiki/Poincaré–Bendixson_theorem)).
- See also: T725, T834

### T836 Topology on number systems
`prove` · stage: reformulate · signals: integers, topology
aka: Furstenberg's proof of the infinitude of primes, evenly spaced integer topology, arithmetic progressions as open sets
- What: puts a topology on Z or N to encode arithmetic facts.
- Fits when: elegant reformulations; teaching cases.
- Lean: the infinitude of primes is Mathlib's `Nat.exists_infinite_primes`; this route is not formalized there.
- Example: Furstenberg's topological proof of the infinitude of primes ([Wikipedia: Furstenberg's proof](https://en.wikipedia.org/wiki/Furstenberg's_proof_of_the_infinitude_of_primes)).
- See also: T823
