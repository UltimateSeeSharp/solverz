# Probability theory
Tail bounds, concentration, couplings, comparison and interpolation, Boolean analysis, scaling limits, random models, and suprema of processes.

### T775 Borel–Cantelli and 0-1 laws
`prove` · stage: argue · signals: random, analytic, integers
aka: Borel–Cantelli lemma, second Borel–Cantelli, Kolmogorov's zero–one law, tail events, almost-sure statements, metric number theory, Khinchin-type theorems
- What: summable probabilities give finitely many occurrences; tail events have probability 0 or 1.
- Fits when: almost-sure statements, metric number theory.
- Lean: Mathlib: `MeasureTheory.measure_limsup_atTop_eq_zero`, `ProbabilityTheory.measure_limsup_eq_one`, `ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`.
- Example: Khinchin-type theorems and Kolmogorov's 0-1 law ([Wikipedia: Borel–Cantelli lemma](https://en.wikipedia.org/wiki/Borel–Cantelli_lemma), [Wikipedia: Kolmogorov's zero–one law](https://en.wikipedia.org/wiki/Kolmogorov's_zero–one_law)).
- See also: T761, T502

### T776 Coupling
`prove` `bound` · stage: argue · signals: random, inequality
aka: coupling method, stochastic domination, monotone coupling, maximal coupling, path coupling, Markov chain convergence, mixing times
- What: realizes two distributions on one space so that a desired comparison holds pointwise.
- Fits when: monotonicity, mixing times, stochastic domination.
- Lean: —
- Example: coupling proofs of Markov chain convergence ([Wikipedia: Coupling](https://en.wikipedia.org/wiki/Coupling_%28probability%29)).
- See also: T782, T778

### T777 Chernoff and large deviations
`bound` · stage: argue · signals: random, inequality, asymptotic
aka: Chernoff bound, Hoeffding's inequality, exponential moment method, moment generating function, Cramér's theorem, rate function, Legendre transform, sub-Gaussian tails
- What: exponential tail bounds through moment generating functions; exact exponential rates.
- Fits when: sums of independent variables far from the mean.
- Lean: Mathlib: `ProbabilityTheory.measure_ge_le_exp_mul_mgf` (Chernoff), `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (Hoeffding).
- Example: Cramér's theorem ([Wikipedia: Chernoff bound](https://en.wikipedia.org/wiki/Chernoff_bound), [Wikipedia: Cramér's theorem](https://en.wikipedia.org/wiki/Cramér's_theorem_%28large_deviations%29)).
- See also: T383, T799, T778

### T778 Gaussian isoperimetry and concentration of measure
`bound` `prove` · stage: argue · signals: random, geometry, inequality
aka: concentration of measure, Lévy's lemma, Borell–Sudakov–Tsirelson, Gaussian isoperimetric inequality, Lipschitz functions concentrate, Dvoretzky's theorem, Johnson–Lindenstrauss lemma, noise stability, almost-Euclidean sections
- What: half-spaces are isoperimetric for Gaussian measure, and Lipschitz functions on high-dimensional spheres or Gaussian space are nearly constant.
- Fits when: high-dimensional probability, noise stability, almost-Euclidean sections, random embeddings.
- Lean: —
- Example: Borell–Sudakov–Tsirelson inequality ([Wikipedia: Gaussian isoperimetric inequality](https://en.wikipedia.org/wiki/Gaussian_isoperimetric_inequality), [Wikipedia: Concentration of measure](https://en.wikipedia.org/wiki/Concentration_of_measure)); Dvoretzky's theorem; Johnson–Lindenstrauss lemma ([Wikipedia: Dvoretzky's theorem](https://en.wikipedia.org/wiki/Dvoretzky's_theorem), [Wikipedia: Johnson–Lindenstrauss lemma](https://en.wikipedia.org/wiki/Johnson–Lindenstrauss_lemma)).
- See also: T384, T615, T777

### T779 Hypercontractivity and Boolean Fourier analysis
`prove` `bound` · stage: argue · signals: set-family, random, threshold
aka: Bonami–Beckner inequality, Bonami lemma, noise operator, analysis of Boolean functions, influences, KKL theorem, Friedgut's junta theorem, sharp thresholds, social choice, Fourier–Walsh expansion
- What: the noise operator is a contraction from L² to L^q, so low-degree functions are tame.
- Fits when: influences, sharp thresholds, social choice.
- Lean: —
- Example: Kahn–Kalai–Linial theorem on influences ([Wikipedia: Analysis of Boolean functions](https://en.wikipedia.org/wiki/Analysis_of_Boolean_functions); O'Donnell, [arXiv:2105.10386](https://arxiv.org/abs/2105.10386)).
- See also: T780, T784, T363, T1054, T1055

### T780 Invariance principles
`prove` · stage: argue · signals: random, matrix, set-family
aka: Lindeberg replacement, Lindeberg swapping, invariance principle, universality, Majority is Stablest, four moment theorem, low-influence functions, Gaussian substitution
- What: swaps variables one at a time for Gaussians, controlling the change by low-order moments.
- Fits when: universality of statistics in random matrices and low-influence functions.
- Lean: Mathlib has a central limit theorem (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`); the invariance principle itself is not there.
- Example: Majority is Stablest (Mossel–O'Donnell–Oleszkiewicz); Tao–Vu four moment theorem ([arXiv:math/0503503](https://arxiv.org/abs/math/0503503), [arXiv:0906.0510](https://arxiv.org/abs/0906.0510), [Tricki: invariance principle first](https://www.tricki.org/article/Establish_an_invariance_principle_first)).
- See also: T779, T781, T1302

### T781 Method of moments
`prove` `compute` · stage: argue · signals: random, matrix, exact-value
aka: moment method, Wigner semicircle law, trace method, closed walks, limit distributions
- What: identifies a limit distribution by matching all moments.
- Fits when: combinatorial expressions for moments (traces of powers, counts).
- Lean: —
- Example: Wigner's semicircle law via counting closed walks ([Wikipedia: Method of moments](https://en.wikipedia.org/wiki/Method_of_moments_%28probability_theory%29), [Wikipedia: Wigner semicircle distribution](https://en.wikipedia.org/wiki/Wigner_semicircle_distribution)).
- See also: T385, T780

### T782 Branching-process comparison
`prove` · stage: argue · signals: graph, random, threshold
aka: Galton–Watson process, local exploration, breadth-first exploration, giant component, percolation on trees, extinction probability
- What: explores a random structure locally as a Galton–Watson tree.
- Fits when: phase transitions in random graphs, percolation on trees.
- Lean: —
- Example: the giant component of G(n, c/n) for c > 1 ([Wikipedia: Galton–Watson process](https://en.wikipedia.org/wiki/Galton–Watson_process), [Wikipedia: Erdős–Rényi model](https://en.wikipedia.org/wiki/Erdős–Rényi_model)).
- See also: T776, T377

### T783 Electrical networks
`prove` `bound` · stage: reformulate · signals: graph, random, matrix
aka: electrical-network analogy, effective resistance, Rayleigh monotonicity, Thomson's principle, energy minimization, recurrence and transience, commute times, random walks on graphs, Doyle–Snell, Kadison–Singer
- What: hitting probabilities and recurrence become resistances; Rayleigh monotonicity compares graphs.
- Fits when: recurrence/transience, commute times, sparsification and spectral statements.
- Lean: on a finite graph, resistances solve a rational linear system, checked exactly by `norm_num` or `decide +kernel`.
- Example: Pólya's recurrence of simple random walk in dimensions 1, 2 ([arXiv:math/0001057](https://arxiv.org/abs/math/0001057)); Spielman's electrical view of graphs on the path to Kadison–Singer ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)).
- See also: T403, T411, T788

### T784 Randomized algorithms as proofs (OSSS)
`prove` · stage: argue · signals: random, threshold, set-family
aka: OSSS inequality, randomized decision trees, revealment, variance by influences, sharp phase transition, random-cluster model, Potts model, percolation
- What: a randomized decision tree bounds variance by influences, giving sharp thresholds.
- Fits when: sharpness of phase transitions in percolation-type models.
- Lean: —
- Example: Duminil-Copin–Raoufi–Tassion sharp phase transition for random-cluster and Potts models ([arXiv:1705.03104](https://arxiv.org/abs/1705.03104), [Wikipedia: Percolation theory](https://en.wikipedia.org/wiki/Percolation_theory)).
- See also: T779, T800

### T785 SLE and conformal invariance
`prove` · stage: argue · signals: random, geometry, analytic
aka: Schramm–Loewner evolution, scaling limits, discrete holomorphic observables, critical percolation, Cardy's formula, Brownian frontier, Mandelbrot's 4/3 conjecture, critical 2D models
- What: scaling limits of planar interfaces are SLE curves driven by Brownian motion; find a discrete observable that becomes harmonic or holomorphic in the limit.
- Fits when: critical 2D models.
- Lean: —
- Example: Smirnov's conformal invariance of critical percolation, identified with SLE₆; Lawler–Schramm–Werner's 4/3 Brownian frontier dimension ([Wikipedia: Schramm–Loewner evolution](https://en.wikipedia.org/wiki/Schramm–Loewner_evolution)).
- See also: T703, T788, T832

### T786 Gaussian and gamma interpolation
`prove` `bound` · stage: argue · signals: random, inequality, analytic
aka: interpolation between models, smart path, Guerra interpolation, Royen's proof, Gaussian correlation inequality, Parisi formula, spin glasses, comparison by differentiation along a path
- What: joins the hard system to a solvable one by a one-parameter path (e.g. independence to full correlation) and controls the derivative along it.
- Fits when: correlation inequalities for Gaussian measures; comparison with a guessed model where the derivative has a sign.
- Lean: —
- Example: Royen's proof of the Gaussian correlation inequality ([arXiv:1408.1028](https://arxiv.org/abs/1408.1028), [arXiv:1512.08776](https://arxiv.org/abs/1512.08776), [Wikipedia: Gaussian correlation inequality](https://en.wikipedia.org/wiki/Gaussian_correlation_inequality)); Guerra's interpolation gave the upper bound in the Parisi formula, completed by Talagrand ([Bolthausen, Bourbaki 948](https://www.numdam.org/item/SB_2004-2005__47__349_0/)).
- See also: T792, T780, T1304

### T787 Exchangeability
`prove` · stage: argue · signals: random, symmetric, graph
aka: de Finetti's theorem, exchangeable sequences, mixtures of i.i.d., exchangeable arrays, graphons
- What: exchangeable sequences are mixtures of i.i.d. sequences; exchangeable arrays give graphons.
- Fits when: symmetric random structures and limits.
- Lean: —
- Example: de Finetti's theorem ([Wikipedia: De Finetti's theorem](https://en.wikipedia.org/wiki/De_Finetti's_theorem)).
- See also: T365

### T788 Brownian motion for harmonic analysis
`prove` · stage: argue · signals: random, pde, analytic
aka: harmonic measure, Kakutani's theorem, Dirichlet problem, exit distributions, probabilistic potential theory, boundary behaviour
- What: harmonic measure equals the exit distribution of Brownian motion.
- Fits when: Dirichlet problems, boundary behaviour.
- Lean: Mathlib defines Brownian motion (Probability/BrownianMotion); the link to harmonic measure is not there.
- Example: Kakutani's probabilistic solution of the Dirichlet problem ([Wikipedia: Harmonic measure](https://en.wikipedia.org/wiki/Harmonic_measure)).
- See also: T783, T671

### T789 Random models of arithmetic dynamics
`prove` · stage: argue · signals: integers, dynamics, random
aka: Collatz conjecture, 3x+1, almost all orbits, random model of a deterministic map, logarithmic density, Syracuse map
- What: replaces a deterministic map by a random model and proves the model's behaviour on a dense set of starting points.
- Fits when: Collatz-type maps, "almost all" statements.
- Lean: —
- Example: Tao: almost all Collatz orbits attain almost bounded values ([arXiv:1909.03562](https://arxiv.org/abs/1909.03562)).
- See also: T312, T497

### T790 Random signs (Khintchine)
`bound` `find` · stage: argue · signals: random, analytic, inequality
aka: Khintchine inequality, Rademacher sums, random ±1 signs, unconditional constructions, randomized counterexamples, Bourgain's random constructions
- What: random ±1 sums have L^p norms comparable to the L² norm.
- Fits when: unconditional constructions, randomized counterexamples.
- Lean: —
- Example: Khintchine inequality in Bourgain's random constructions ([Wikipedia: Khintchine inequality](https://en.wikipedia.org/wiki/Khintchine_inequality), [arXiv:2009.06736](https://arxiv.org/abs/2009.06736)).
- See also: T791, T386

### T791 Discrepancy via partial colouring
`prove` `find` `bound` · stage: argue · signals: set-family, colouring, random
aka: Spencer's six standard deviations, partial colouring lemma, entropy method, Beck–Fiala, SDP-guided random walks, constructive discrepancy, Bansal's algorithm, edge-walk partial colouring, Lovett–Meka
- What: colours half the elements with small discrepancy, then recurses (entropy or Gaussian walks).
- Fits when: balanced colourings of set systems.
- Lean: a found colouring's discrepancy is a finite check by `decide +kernel`.
- Example: Spencer's six-standard-deviations theorem and Bansal's algorithmic version ([Wikipedia: Discrepancy theory](https://en.wikipedia.org/wiki/Discrepancy_theory), [arXiv:1002.2259](https://arxiv.org/abs/1002.2259)); Lovett–Meka's edge walk ([arXiv:1203.5747](https://arxiv.org/abs/1203.5747)).
- See also: T790, T364, T1, T1076

### T792 Gaussian comparison (Slepian)
`bound` · stage: argue · signals: random, inequality, matrix
aka: Slepian's lemma, suprema of Gaussian processes, random-matrix norms, escape through a mesh
- What: if two Gaussian vectors have equal variances and ordered covariances, their maxima are stochastically ordered.
- Fits when: suprema of Gaussian processes, random-matrix norms, escape-through-mesh arguments.
- Lean: —
- Example: [Wikipedia: Slepian's lemma](https://en.wikipedia.org/wiki/Slepian%27s_lemma).
- See also: T793, T786

### T793 Chaining (Dudley's entropy integral)
`bound` · stage: argue · signals: random, analytic, inequality
aka: Dudley's entropy integral, generic chaining, covering numbers, metric entropy, suprema of processes, uniform bounds
- What: bounds the expected supremum of a process by an integral of log covering numbers over scales.
- Fits when: uniform bounds over infinite index sets.
- Lean: —
- Example: [Wikipedia: Dudley's entropy integral](https://en.wikipedia.org/wiki/Dudley%27s_entropy_integral).
- See also: T792, T620

### T794 BK inequality
`bound` · stage: argue · signals: random, set-family, inequality
aka: van den Berg–Kesten inequality, Reimer's inequality, disjoint occurrence, percolation, product spaces, negative correlation
- What: the probability that two events occur disjointly is at most the product of their probabilities.
- Fits when: percolation and product spaces, where FKG gives the other direction.
- Lean: —
- Example: [Wikipedia: Van den Berg–Kesten inequality](https://en.wikipedia.org/wiki/Van_den_Berg%E2%80%93Kesten_inequality).
- See also: T372, T784
