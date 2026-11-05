# Probabilistic method
Random constructions and their estimates in combinatorics: first and second moments, alteration, local lemmas, Janson, concentration, Poisson approximation, tailored distributions, random-algebraic hybrids, random regular graphs.

### T374 First moment method
`find` `bound` · stage: argue · signals: random, construction, pseudorandom
aka: expectation method, union bound, expected number of bad configurations below 1, Erdős's Ramsey lower bound, diagonal Ramsey numbers
- What: show the expected number of bad configurations is < 1, or E[X] ≥ t.
- Fits when: extremal examples look spread out and unstructured.
- Lean: on a finite space, count instead of integrating (`Finset.exists_lt_of_sum_lt`); measure form: Mathlib's `measure_biUnion_finset_le` (union bound).
- Example: Erdős's 1947 exponential lower bound for diagonal Ramsey numbers ([Wikipedia: Probabilistic method](https://en.wikipedia.org/wiki/Probabilistic_method)).
- See also: T326, T376, T377, T312

### T375 Linearity of expectation with a random parameter
`find` `bound` · stage: argue · signals: random, construction
aka: random dilation, random shift, random ordering, indicator variables, Szele's tournaments, Hamiltonian paths in tournaments, Buffon's needle, Barbier's noodle
- What: average a count over a random dilation, shift or ordering to find a good one.
- Fits when: the quantity is a sum of indicator variables with computable marginals.
- Lean: Mathlib: `MeasureTheory.integral_finsetSum`; on finite spaces swap sums with `Finset.sum_comm`.
- Example: Szele's tournaments with many Hamiltonian paths (expected count of a random tournament); Barbier's solution of Buffon's needle via the noodle ([Wikipedia: Probabilistic method](https://en.wikipedia.org/wiki/Probabilistic_method), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T374, T326

### T376 Alteration
`find` `bound` · stage: construct · signals: random, graph, construction
aka: deletion method, random object then repair, high girth and high chromatic number, Erdős's graphs
- What: take a random object with few defects, then delete or repair them.
- Fits when: random objects are good except for a small number of local defects.
- Lean: the random step as counting (T374); the repair as an explicit function on finite objects.
- Example: Erdős's graphs with arbitrarily high girth and chromatic number ([Wikipedia: Probabilistic method](https://en.wikipedia.org/wiki/Probabilistic_method)).
- See also: T374, T362

### T377 Second moment method
`prove` · stage: argue · signals: random, threshold
aka: Chebyshev's inequality, variance method, Paley–Zygmund inequality, thresholds, percolation on trees
- What: show Var X = o((EX)²) so X > 0 with high probability; Paley–Zygmund gives positive probability.
- Fits when: thresholds where existence is likely but not guaranteed by the first moment.
- Lean: Mathlib: `ProbabilityTheory.meas_ge_le_variance_div_sq` (Chebyshev); a grep finds no Paley–Zygmund.
- Example: bond percolation on the infinite binary tree has an infinite root cluster with positive probability for every p ∈ (1/2, 1] ([Wikipedia: Second moment method](https://en.wikipedia.org/wiki/Second_moment_method), [Wikipedia: Paley–Zygmund inequality](https://en.wikipedia.org/wiki/Paley–Zygmund_inequality), [Tricki: second-moment method](https://www.tricki.org/article/The_second-moment_method)).
- See also: T378, T374, T382

### T378 Small subgraph conditioning
`prove` · stage: argue · signals: graph, random, sparse
aka: Robinson–Wormald method, conditioning on short cycle counts, random regular graphs, Hamiltonicity of random regular graphs, contiguity
- What: condition on the counts of short cycles to explain the variance of a count; then the second moment method works.
- Fits when: the second moment of a count is too large only because of short-cycle fluctuations (random regular graphs).
- Lean: —
- Example: Robinson–Wormald's Hamiltonicity of random regular graphs, made quantitative by Johnson–Paquette ([arXiv:1307.4858](https://arxiv.org/abs/1307.4858)).
- See also: T377, T390

### T379 Lovász local lemma
`find` `prove` · stage: argue · signals: random, local-constraints, colouring
aka: LLL, local lemma, dependency graph, rare bad events, hypergraph 2-colouring, SAT with bounded occurrences
- What: if bad events are each unlikely and mostly independent, with positive probability none occurs.
- Fits when: many rare local constraints (colourings, SAT, hypergraph 2-colouring) with bounded dependency.
- Lean: a grep finds no local lemma in Mathlib; a found object checks by `decide +kernel`.
- Example: 11n points on a circle, n colours used 11 times each: one point of every colour can be chosen with no two adjacent ([Wikipedia: Lovász local lemma](https://en.wikipedia.org/wiki/Lovász_local_lemma)).
- See also: T380, T381, T1

### T380 Lopsided local lemma
`find` `prove` · stage: argue · signals: random, order, local-constraints
aka: lopsidependency, negative dependence, local lemma for random permutations, injections, matchings, Latin transversals
- What: the local lemma with negative dependence (lopsidependency), as in random permutations and injections.
- Fits when: bad events are not independent but are positively hindered by each other (permutations, matchings).
- Lean: —
- Example: Harris's criteria for the lopsided LLL in the Moser–Tardos framework ([arXiv:1610.02420](https://arxiv.org/abs/1610.02420)).
- See also: T379, T381

### T381 Algorithmic local lemma and entropy compression
`find` · stage: construct · signals: random, local-constraints, construction
aka: Moser–Tardos resampling, constructive local lemma, entropy compression, entropy compression beyond the LLL, algorithmic LLL, Thue choice number, nonrepetitive colouring, acyclic edge colouring
- What: show a random-fixing algorithm halts, since a long run would compress its random bits; the resampling algorithm doubles as a practical local-search engine for find problems.
- Fits when: you want a construction (or a better constant) from the LLL.
- Lean: the output is a witness checked by `decide +kernel` (T118); the halting argument need not be formalized.
- Example: Moser–Tardos constructive general local lemma ([arXiv:0903.0544](https://arxiv.org/abs/0903.0544)); Moser 2008 ([arXiv:0810.4812](https://arxiv.org/abs/0810.4812)); beyond the LLL: Thue choice number ≤ 4 ([Grytczuk–Kozik–Micek](https://arxiv.org/abs/1103.3809)), acyclic edge colouring with 4Δ−4 colours ([Esperet–Parreau](https://arxiv.org/abs/1206.1535)).
- See also: T379, T380, T768

### T382 Janson inequalities
`bound` · stage: argue · signals: random, graph, threshold
aka: Janson's inequality, lower tails, positively correlated events, probability G(n,p) is triangle-free, clique number concentration
- What: the probability that no member of a family of positively correlated events occurs is about exp(-μ + Δ).
- Fits when: small-probability lower tails for subgraph counts.
- Lean: —
- Example: the probability G(n,p) is triangle-free, and clique number concentration ([Wikipedia: Janson inequality](https://en.wikipedia.org/wiki/Janson_inequality)).
- See also: T372, T377, T385

### T383 Martingales: concentration and optional stopping
`bound` `prove` · stage: argue · signals: random, inequality
aka: Azuma's inequality, Azuma–Hoeffding, McDiarmid's bounded differences inequality, Doob martingale, exposure martingale, optional stopping theorem, gambler's ruin, hitting probabilities
- What: a function with bounded differences of independent inputs is concentrated around its mean; a fair-game process has constant expectation at stopping times.
- Fits when: random graph invariants that change little per vertex or edge; hitting probabilities and gambler's-ruin computations.
- Lean: Mathlib: martingales and optional stopping in `Probability/Martingale` (`OptionalStopping.lean`); Azuma–Hoeffding as `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` (`Probability/Moments/SubGaussian.lean`).
- Example: concentration of Lipschitz functions on the symmetric group via a martingale over revealed positions ([Tricki: How to use martingales](https://www.tricki.org/article/How_to_use_martingales), [Wikipedia: Azuma's inequality](https://en.wikipedia.org/wiki/Azuma's_inequality), [Wikipedia: McDiarmid's inequality](https://en.wikipedia.org/wiki/McDiarmid's_inequality)); impossibility of winning betting systems; exit probabilities of random walks ([Wikipedia: Optional stopping theorem](https://en.wikipedia.org/wiki/Optional_stopping_theorem)).
- See also: T384, T362, T777

### T384 Talagrand's inequality
`bound` · stage: argue · signals: random, inequality
aka: Talagrand's convex-distance inequality, certifiable functions, concentration around the median, longest increasing subsequence
- What: concentration for certifiable functions of product measure, around the median at scale √(certificate size).
- Fits when: the event "X ≥ t" has small witnesses.
- Lean: —
- Example: Talagrand's convex-distance inequality, the standard route to concentration of certifiable statistics such as longest increasing subsequences ([Wikipedia: Talagrand's concentration inequality](https://en.wikipedia.org/wiki/Talagrand's_concentration_inequality)).
- See also: T383, T778

### T385 Poisson paradigm
`bound` `compute` · stage: argue · signals: random, asymptotic
aka: Stein–Chen method, Poisson approximation, Stein's method, small subgraph counts, fixed points of permutations, rare dependent events
- What: counts of rare weakly dependent events are approximately Poisson, with explicit error.
- Fits when: distributions of small subgraph counts or fixed points.
- Lean: —
- Example: Chen's Poisson version of Stein's method for counts of rare dependent events ([Wikipedia: Stein's method](https://en.wikipedia.org/wiki/Stein's_method)).
- See also: T382, T781

### T386 Unusual distributions
`find` · stage: construct · signals: random, construction
aka: non-uniform random constructions, tailored distributions, biased sampling
- What: sample from a tailored, non-uniform distribution that favours the structure you want.
- Fits when: the uniform distribution wastes probability on useless objects.
- Lean: on finite spaces a weighted average (`Finset.sum` with weights) replaces the expectation.
- Example: the Tricki's examples of nonuniform random constructions ([Tricki: Unusual choices of probability distribution](https://www.tricki.org/article/Unusual_choices_of_probability_distribution)).
- See also: T374, T387

### T387 Random refinement
`prove` `find` · stage: argue · signals: random, dense
aka: random sparsification, random subset, pass to a random substructure
- What: pass to a random subset that preserves density but raises the frequency of the desired property.
- Fits when: a property holds on average but needs concentration in a substructure.
- Lean: —
- Example: Tricki's random refinement principle ([Tricki: randomly refining](https://www.tricki.org/article/To_increase_the_occurrence_of_a_property_in_a_set_try_randomly_refining_that_set_in_a_way_that_favors_the_property)).
- See also: T386, T356

### T388 Random and algebraic hybrids
`find` `bound` · stage: construct · signals: graph, finite-field, random, construction
aka: seed randomness with algebraic structure, random subgraphs of algebraic graphs, pseudorandom graphs, Hermitian unital, r(4,t), off-diagonal Ramsey numbers, multicolour Ramsey lower bounds
- What: take random subgraphs of algebraically defined pseudorandom graphs; the algebra fixes the hard constraint, random choices destroy the rest.
- Fits when: pure random constructions lose polynomial factors, or stall at a known exponent.
- Lean: the final graph as a witness (T118); `decide +kernel` only at small sizes.
- Example: Mattheus–Verstraete's r(4,t) = Ω(t³/log⁴ t) from random subgraphs of a Hermitian-unital graph; Conlon–Ferber multicolour Ramsey lower bounds ([arXiv:2306.04007](https://arxiv.org/abs/2306.04007), [arXiv:2009.10458](https://arxiv.org/abs/2009.10458)).
- See also: T366, T367, T434, T91

### T389 Entropy versus energy
`bound` `prove` · stage: argue · signals: random, geometry
aka: first moment over configurations, union bound over shapes, counting contours, percolation estimates, Peierls-type counting
- What: trade the number of configurations against the probability of each.
- Fits when: percolation-style or union-bound-over-shapes estimates.
- Lean: —
- Example: percolation estimates in the Tricki article ([Tricki: Entropy vs. energy](https://www.tricki.org/article/Entropy_vs_energy)).
- See also: T374, T800

### T390 Configuration model and switchings
`prove` `compute` · stage: argue · signals: graph, random, sparse
aka: pairing model, half-edge pairing, random graphs with given degrees, random regular graphs, switching method, counting regular graphs
- What: generate graphs with a degree sequence by pairing half-edges, then switch edges to remove loops and multiple edges while controlling the distribution.
- Fits when: random graphs with given degrees; counting regular graphs; transferring results to simple graphs.
- Lean: —
- Example: Janson: simple switchings give an almost uniform simple graph ([arXiv:1901.09744](https://arxiv.org/abs/1901.09744), [Wikipedia: Configuration model](https://en.wikipedia.org/wiki/Configuration_model)).
- See also: T378, T377
