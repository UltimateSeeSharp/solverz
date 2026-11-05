# Statistical-mechanics methods
Proof methods from mathematical physics: contours, cluster expansions, integrable lattice models, Gaussian and Grassmann integrals, zero counting for random functions, and bootstrap bounds.

### T800 Peierls contour argument
`prove` `bound` · stage: argue · signals: random, graph, threshold
aka: Peierls droplets, contours, energy versus entropy, Ising model, long-range order, spontaneous magnetization, phase transitions, rare large defects
- What: bounds the probability of a large defect by summing over the contours that surround it (entropy of contours against energy cost).
- Fits when: proving long-range order, a phase transition, or that large bad regions are rare.
- Lean: —
- Example: Peierls (1936) proved spontaneous magnetization of the 2D Ising model with "Peierls droplets" ([Wikipedia: Ising model](https://en.wikipedia.org/wiki/Ising_model)).
- See also: T801, T784

### T801 Cluster expansion and algorithmic Pirogov–Sinai theory
`compute` `bound` · stage: argue · signals: graph, random, polynomial
aka: Mayer expansion, polymer models, Pirogov–Sinai theory, zero-free regions, Barvinok's method, truncated Taylor series, hard-core model, approximate counting at low temperature
- What: expands log Z as a convergent series over polymers or contours; convergence gives zero-free regions and analyticity, and truncation gives counting algorithms.
- Fits when: approximate counting or sampling at low temperature or high fugacity, where the usual methods fail.
- Lean: —
- Example: Helmuth–Perkins–Regts combine Pirogov–Sinai contours with Barvinok's truncated Taylor series ([arXiv:1806.11548](https://arxiv.org/abs/1806.11548)); Jenssen–Keevash–Perkins count hard-core configurations on bipartite expanders ([arXiv:1807.04804](https://arxiv.org/abs/1807.04804)); Mayer's expansion ([Wikipedia: Cluster expansion](https://en.wikipedia.org/wiki/Cluster_expansion)).
- See also: T800, T403, T1304

### T802 Exactly solvable lattice models (Yang–Baxter)
`compute` `prove` · stage: argue · signals: matrix, exact-value, symmetric
aka: Yang–Baxter equation, integrable models, six-vertex model, alternating sign matrices, ASM enumeration, tilings, lattice paths, partition functions
- What: encodes the objects as states of an integrable model; the Yang–Baxter equation gives symmetry and determinant formulas for the partition function.
- Fits when: an exact count of matrices, tilings or lattice paths with a product formula.
- Lean: the product formula for small n against a brute-force count by `decide +kernel`; the general proof by hand.
- Example: Kuperberg's proof of the alternating-sign-matrix count via the six-vertex model ([arXiv:math/9712207](https://arxiv.org/abs/math/9712207)).
- See also: T408, T447

### T803 Gaussian integrals and Wick pairings
`compute` · stage: argue · signals: graph, exact-value, random
aka: Wick's theorem, Isserlis's theorem, matrix integrals, ribbon graphs, maps on surfaces, genus expansion, Kontsevich, Witten's conjecture, matrix Airy function
- What: a Gaussian moment is a sum over pairings (Isserlis/Wick), so matrix integrals become generating functions for glued polygons (ribbon graphs).
- Fits when: counting maps, ribbon graphs or pairings by genus.
- Lean: —
- Example: Isserlis's theorem ([Wikipedia: Isserlis's theorem](https://en.wikipedia.org/wiki/Isserlis%27s_theorem), [Wikipedia: Wick's theorem](https://en.wikipedia.org/wiki/Wick%27s_theorem)); Kontsevich proved Witten's conjecture with ribbon graphs and the matrix Airy function ([Wikipedia: Witten conjecture](https://en.wikipedia.org/wiki/Witten_conjecture)).
- See also: T781, T447, T1307

### T804 Grassmann (fermionic) integrals for counting
`compute` `prove` · stage: argue · signals: graph, matrix, exact-value
aka: Berezin integration, anticommuting variables, fermionic integrals, determinants, Pfaffians, spanning forests, matrix-tree theorem generalizations
- What: anticommuting variables turn determinants, Pfaffians and forest counts into integrals that can be manipulated algebraically.
- Fits when: generalizing matrix-tree or Pfaffian counts.
- Lean: —
- Example: Caracciolo–Jacobsen–Saleur–Sokal represent spanning forests by a Grassmann integral ([arXiv:cond-mat/0403271](https://arxiv.org/abs/cond-mat/0403271)).
- See also: T408, T803

### T805 Kac–Rice formula
`compute` `bound` · stage: argue · signals: polynomial, random, analytic
aka: Kac–Rice, Rice formula, expected number of zeros, real roots of random polynomials, critical points of random landscapes, Edelman–Kostlan
- What: the expected number of zeros of a random function is an integral of a local density.
- Fits when: real roots of random polynomials, critical points of random landscapes.
- Lean: —
- Example: Edelman–Kostlan: the expected number of real zeros is the length of the moment curve's projection ([arXiv:math/9501224](https://arxiv.org/abs/math/9501224)).
- See also: T701, T594

### T806 Bootstrap by SDP
`bound` · stage: relax · signals: geometry, inequality, symmetric
aka: conformal bootstrap, modular bootstrap, crossing symmetry, positivity constraints, spectral bounds, 3D Ising exponents, Cohn–Elkies, sphere packing
- What: imposes symmetry and positivity on unknown spectral data and uses semidefinite programs to exclude regions; its dual is the same object as an LP bound in geometry.
- Fits when: a spectral or packing bound whose primal is crossing or modular invariance.
- Lean: a bound counts only with an exact dual certificate (T124, T50).
- Example: the 3D Ising critical exponents ([Wikipedia: Conformal bootstrap](https://en.wikipedia.org/wiki/Conformal_bootstrap)); the modular bootstrap bound maps exactly to the Cohn–Elkies sphere-packing bound ([arXiv:1905.01319](https://arxiv.org/abs/1905.01319)).
- See also: T50, T53, T124
