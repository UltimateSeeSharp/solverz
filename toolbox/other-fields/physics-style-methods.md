# Physics-style methods
Heuristics and reformulations from physics that predict an answer, test an estimate or recast a problem; rigorous statistical-mechanics proof methods are in pure math.

### T1300 Dimensional analysis and scaling
`prove` `bound` · stage: judge · signals: analytic, inequality
aka: scaling argument, units, rescaling, homogeneity, scale invariance, Sobolev exponents, Gagliardo–Nirenberg, amplification, sanity check of an estimate
- What: gives each variable a unit (length, amplitude, n, N) and discards any estimate whose sides scale differently; optimizing a lossy inequality over rescalings sharpens it.
- Fits when: a conjectured or claimed inequality needs a quick check, or its exponents a guess.
- Lean: —
- Example: Tao derives the Sobolev condition d/q = d/p − 1 by scaling and amplifies the inhomogeneous inequality into Gagliardo–Nirenberg ([Tao](https://terrytao.wordpress.com/2012/12/29/a-mathematical-formalisation-of-dimensional-analysis/)).
- See also: T1303, T1323

### T1301 Perturbation from a solvable point
`prove` `bound` `compute` · stage: explore
aka: perturbation theory, perturbation series, small parameter, solvable case, integrable case, degenerate case, resonances, small divisors, KAM theory
- What: writes the answer as the exact solution of a simpler problem plus corrections in a small parameter.
- Fits when: a degenerate, integrable or extremal case is solvable; track how the answer moves from it; where the series diverges (resonances, small divisors) is where the real difficulty sits.
- Lean: —
- Example: celestial-mechanics perturbation series led to KAM theory, where only "sufficiently irrational" tori survive ([Wikipedia: Perturbation theory](https://en.wikipedia.org/wiki/Perturbation_theory); [Wikipedia: KAM theorem](https://en.wikipedia.org/wiki/Kolmogorov%E2%80%93Arnold%E2%80%93Moser_theorem)).
- See also: T85, T1310

### T1302 Random-model universality
`prove` `compute` · stage: explore
aka: universality, random model heuristics, random matrix theory, GUE, ensemble with the same symmetry, pair correlation, Montgomery–Dyson, Odlyzko, zeta zeros, random graphs, predicted constants
- What: predicts statistics of a complicated deterministic system from a random ensemble with the same symmetry.
- Fits when: a constant or conjecture needs a prediction; pick the right random model (random matrices, random graphs), then compare numerically.
- Lean: — (predictions only).
- Example: Montgomery's pair correlation of zeta zeros equals Dyson's GUE formula; Odlyzko's computations agreed ([Wikipedia: Montgomery's pair correlation conjecture](https://en.wikipedia.org/wiki/Montgomery%27s_pair_correlation_conjecture)).
- See also: T1303, T1328

### T1303 Mean-field and first-moment heuristics
`bound` · stage: explore · signals: threshold
aka: mean-field theory, average interaction, expected count, first moment, expectation threshold, Kahn–Kalai conjecture, Park–Pham, log factor
- What: replaces all interactions on one component by their average and ignores fluctuations; most accurate in high dimension or with long-range interactions.
- Fits when: a threshold or bound needs a predicted value: the expected count is the prediction, and the theorem is often that the truth is within a log factor of it.
- Lean: —
- Example: the Kahn–Kalai expectation threshold is such an average; Park–Pham proved the true threshold is at most a log factor above it ([Wikipedia: Mean-field theory](https://en.wikipedia.org/wiki/Mean-field_theory); [Quanta](https://www.quantamagazine.org/elegant-six-page-proof-reveals-the-emergence-of-random-structure-20220425/)).
- See also: T1302, T1304, T1323

### T1304 Replica and cavity methods
`bound` `compute` · stage: explore · signals: random, threshold
aka: replica trick, replica symmetry breaking, one-step RSB, 1RSB, cavity method, tree recursions, spin glasses, disordered systems, free energy, random k-SAT threshold, Ding–Sly–Sun
- What: non-rigorous statistical-physics calculations (n → 0 replicas, replica symmetry breaking, tree recursions) that predict free energies and thresholds of disordered systems.
- Fits when: a random constraint problem needs a target value; take the physics value as the target, then prove matching bounds (interpolation, moment methods, tree recursions).
- Lean: —
- Example: the one-step RSB prediction is the exact random k-SAT threshold, proved for large k by Ding–Sly–Sun ([arXiv:1411.0650](https://arxiv.org/abs/1411.0650); [Wikipedia: Replica trick](https://en.wikipedia.org/wiki/Replica_trick); [Wikipedia: Spin glass](https://en.wikipedia.org/wiki/Spin_glass)).
- See also: T1303

### T1305 Dualities and self-duality
`compute` `prove` · stage: reformulate · signals: exact-value
aka: duality transform, self-dual, planar dual, mirror symmetry, T-duality, bond percolation threshold 1/2, curve counts, exact values
- What: trades a hard description for an equivalent easy one (self-duality, mirror symmetry, T-duality); a self-dual case pins an exact value.
- Fits when: a transform might swap the hard quantity with a computable one, or the problem looks equal to its own dual.
- Lean: —
- Example: self-duality of the square lattice forces bond-percolation threshold 1/2 ([Wikipedia: Percolation threshold](https://en.wikipedia.org/wiki/Percolation_threshold)); mirror symmetry turned curve counts into computable quantities on the mirror ([Wikipedia: Mirror symmetry (string theory)](https://en.wikipedia.org/wiki/Mirror_symmetry_(string_theory))).
- See also: T1307

### T1306 Symmetry gives conservation (Noether)
`prove` `find` `compute` · stage: reformulate · signals: symmetric
aka: Noether's theorem, conserved quantity, invariant from a symmetry, continuous symmetry, unreachability, symmetry reduction, Noperthedron
- What: every continuous symmetry of the action yields a conserved quantity.
- Fits when: the problem has a symmetry: look for the invariant it implies; invariants rule out reachability, symmetries shrink search spaces.
- Lean: —
- Example: [Wikipedia: Noether's theorem](https://en.wikipedia.org/wiki/Noether%27s_theorem); the Noperthedron proof reduces its 5-parameter search by the polyhedron's symmetries ([arXiv:2508.18475](https://arxiv.org/html/2508.18475)).
- See also: T24, T27

### T1307 Quantum field theory as a conjecture engine
`prove` `compute` · stage: explore
aka: physics conjectures, path integrals, gauge theory, exact formulas, Witten conjecture, 2D gravity, KdV, Kontsevich, ribbon graphs, matrix integral, Seiberg–Witten invariants, Donaldson theory
- What: path integrals and gauge theories produce invariants and exact formulas before mathematics can define them.
- Fits when: a physics theory computes the quantity; mine it for exact conjectural formulas, then prove them by combinatorial models or new structures.
- Lean: —
- Example: Witten's 2D-gravity conjecture (KdV), proved by Kontsevich with ribbon graphs and a matrix integral ([Wikipedia: Witten conjecture](https://en.wikipedia.org/wiki/Witten_conjecture)); Seiberg–Witten invariants did Donaldson theory's job with compact moduli spaces ([Wikipedia: Seiberg–Witten invariants](https://en.wikipedia.org/wiki/Seiberg%E2%80%93Witten_invariants)).
- See also: T1305, T1322

### T1308 Physical models for discovery
`compute` `prove` · stage: explore
aka: mechanical method, lever, balance, Archimedes, The Method, physical reading, energy, flow, charge, guess then prove
- What: computes a quantity by imagining a physical system (lever, energy, flow, charge) that must balance; the proof comes separately.
- Fits when: an area, volume, sum or extremal value needs a guess.
- Lean: —
- Example: Archimedes balanced slices on a lever to find the parabola-segment area and the sphere volume, then proved them by exhaustion ([Wikipedia: The Method of Mechanical Theorems](https://en.wikipedia.org/wiki/The_Method_of_Mechanical_Theorems)).
- See also: T1309

### T1309 Thought experiments
`prove` · stage: reformulate
aka: Gedankenexperiment, imagined configuration, extreme configuration, contradiction, Galileo, falling bodies
- What: derives a contradiction from imagined configurations without running anything.
- Fits when: a claim forbids some configuration; assume the claim, construct the extreme configuration it forbids, look for the absurdity.
- Lean: —
- Example: Galileo tied a light body to a heavy one to refute "heavier falls faster" ([Wikipedia: Thought experiment](https://en.wikipedia.org/wiki/Thought_experiment)).
- See also: T1308

### T1310 Measure before you theorise
`find` `prove` `bound` `compute` · stage: explore
aka: compute first, numerical evidence, test inequalities numerically, find the needed lemma, de Branges, Gautschi, Jacobi sums, Feigenbaum δ
- What: computes the phenomenon first: constants and inequalities numerically, to decide what to prove and to expose the needed lemma.
- Fits when: it is unclear what exactly to prove, or which lemma a proof needs.
- Lean: — (evidence only).
- Example: Gautschi checked de Branges's Jacobi-sum inequalities by computer up to n = 30 ([Wikipedia: De Branges's theorem](https://en.wikipedia.org/wiki/De_Branges%27s_theorem)); Feigenbaum found δ numerically ([Wikipedia: Feigenbaum constants](https://en.wikipedia.org/wiki/Feigenbaum_constants)).
- See also: T76, T83, T1314, T1333
