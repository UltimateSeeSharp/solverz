# Extremal combinatorics
Turán-type and density problems: symmetrization, stability, regularity and removal, containers, absorption, nibble and random greedy, spread measures, entropy, graph limits, algebraic constructions, correlation inequalities.

### T350 Symmetrization (Zykov)
`prove` `bound` · stage: argue · signals: graph, inequality, classification
aka: Zykov symmetrization, vertex cloning, complete multipartite extremal graphs, Turán's theorem, Turán graph, clique-free graphs
- What: repeatedly replace a vertex by a clone of a better vertex; the extremal graph becomes complete multipartite.
- Fits when: maximizing edges or cliques under a forbidden-clique condition.
- Lean: Mathlib proves Turán's theorem (`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`, `SimpleGraph.CliqueFree.card_edgeFinset_le` in `Combinatorics/SimpleGraph/Extremal/Turan.lean`).
- Example: a proof of Turán's theorem ([Wikipedia: Turán's theorem](https://en.wikipedia.org/wiki/Turán's_theorem)).
- See also: T351, T354

### T351 Stability method
`prove` `bound` · stage: argue · signals: graph, classification, near-miss
aka: Erdős–Simonovits stability, near-extremal structure, exact Turán numbers, cleaning up, Erdős–Stone theorem
- What: show near-extremal objects are close to the extremal one, then clean up the exact case.
- Fits when: the extremal structure is unique and the exact answer is wanted for large n.
- Lean: the exact Turán theorem is in Mathlib (T350); a grep finds no Erdős–Stone theorem.
- Example: the Erdős–Stone theorem, whose Erdős–Simonovits stability form drives exact Turán results ([Wikipedia: Erdős–Stone theorem](https://en.wikipedia.org/wiki/Erdős–Stone_theorem)).
- See also: T350, T352

### T352 Szemerédi regularity lemma and counting lemma
`prove` · stage: argue · signals: graph, dense, asymptotic
aka: regularity lemma, ε-regular pairs, counting lemma, triangle removal lemma, Roth's theorem, corners theorem, Ruzsa–Szemerédi (6,3) problem, tower-type bounds
- What: partition any large graph into boundedly many random-like pairs, then count subgraphs as in a random graph.
- Fits when: dense graphs, qualitative or tower-type bounds acceptable.
- Lean: Mathlib: `szemeredi_regularity`, `SimpleGraph.triangle_removal`, `roth_3ap_theorem`, `corners_theorem` (`Combinatorics/SimpleGraph/Regularity`, `Triangle/Removal.lean`, `Combinatorics/Additive/Corner/Roth.lean`).
- Example: the triangle removal lemma and through it Roth's theorem and the Ruzsa–Szemerédi (6,3) theorem ([Wikipedia: Szemerédi regularity lemma](https://en.wikipedia.org/wiki/Szemerédi_regularity_lemma), [Wikipedia: Triangle removal lemma](https://en.wikipedia.org/wiki/Triangle_removal_lemma), [Wikipedia: Ruzsa–Szemerédi problem](https://en.wikipedia.org/wiki/Ruzsa–Szemerédi_problem)).
- See also: T353, T354, T413, T412

### T353 Hypergraph regularity and removal
`prove` · stage: argue · signals: set-family, additive, dense
aka: hypergraph removal lemma, simplex removal, hypergraph regularity lemma, multidimensional Szemerédi theorem
- What: the k-uniform analogue; few copies of a simplex imply it can be deleted by removing few edges.
- Fits when: multidimensional density problems.
- Lean: Mathlib's regularity lemma is for graphs (T352).
- Example: Tao's hypergraph removal lemma, giving Szemerédi's theorem and its multidimensional form ([arXiv:math/0503572](https://arxiv.org/abs/math/0503572)).
- See also: T352, T414, T823

### T354 Supersaturation
`prove` `bound` · stage: argue · signals: graph, dense, inequality
aka: Erdős–Simonovits supersaturation, many copies above the threshold, counting versions, removal corollaries
- What: above the extremal threshold there are not just one but a positive fraction of the expected copies.
- Fits when: counting versions, or feeding container and removal arguments.
- Lean: Mathlib: `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset` (many triangles in a graph far from triangle-free).
- Example: removal-lemma corollaries and Erdős–Simonovits supersaturation ([Wikipedia: Triangle removal lemma](https://en.wikipedia.org/wiki/Triangle_removal_lemma)).
- See also: T352, T357

### T355 Blow-up lemma
`prove` `find` · stage: argue · signals: graph, dense, construction
aka: Komlós–Sárközy–Szemerédi, super-regular pairs, spanning subgraphs, Pósa–Seymour conjecture, powers of Hamilton cycles, bounded-degree spanning trees
- What: in a super-regular pair, bounded-degree spanning graphs embed as if the pair were complete.
- Fits when: embedding spanning structures (Hamilton cycles, powers, trees) in dense graphs.
- Lean: —
- Example: Komlós–Sárközy–Szemerédi proofs of the Pósa–Seymour conjecture for large n ([Wikipedia: Blow-up lemma](https://en.wikipedia.org/wiki/Blow-up_lemma)).
- See also: T352, T358

### T356 Dependent random choice
`prove` `bound` · stage: argue · signals: graph, random, sparse
aka: common neighbourhoods, rich subsets, bipartite Turán numbers, Ramsey numbers of sparse graphs, embedding bounded-degree bipartite graphs
- What: pick a random small set and take its common neighbourhood; almost all small subsets there have many common neighbours.
- Fits when: embedding sparse bipartite graphs or finding rich subsets in dense graphs.
- Lean: on finite graphs the averaging step is counting (`Finset.exists_lt_of_sum_lt`).
- Example: Turán numbers of bipartite graphs with bounded degree on one side; Ramsey numbers of sparse graphs ([arXiv:0909.3271](https://arxiv.org/abs/0909.3271)).
- See also: T374, T366

### T357 Hypergraph containers
`prove` `bound` `compute` · stage: argue · signals: set-family, graph, sparse, threshold
aka: container method, Balogh–Morris–Samotij, Saxton–Thomason, container applications, independent sets in hypergraphs, counting H-free graphs, counting sum-free sets, sparse random Szemerédi theorem, sparse random Erdős–Stone, list colouring
- What: all independent sets of a hypergraph lie in few "containers", each nearly independent.
- Fits when: counting H-free graphs or sum-free sets, sparse random analogues of extremal theorems, list colouring.
- Lean: —
- Example: sparse random versions of Szemerédi's and Erdős–Stone theorems ([arXiv:1204.6530](https://arxiv.org/abs/1204.6530), [arXiv:1204.6595](https://arxiv.org/abs/1204.6595)); applications toolkit in the BMS survey ([arXiv:1801.04584](https://arxiv.org/abs/1801.04584)).
- See also: T354, T363, T415

### T358 Absorbing method
`prove` `find` · stage: argue · signals: graph, set-family, construction
aka: absorbers, absorption, leftover swallowing, Steiner triple systems of high girth, Erdős–Faber–Lovász conjecture, spanning structures, exact decompositions
- What: set aside a flexible "absorber" structure first, cover almost everything by other means, then let the absorber swallow the leftover.
- Fits when: exact spanning or decomposition results where random or greedy methods leave a small remainder.
- Lean: —
- Example: Erdős's 1973 conjecture on Steiner triple systems of arbitrarily high girth; Erdős–Faber–Lovász for large n ([arXiv:2201.04554](https://arxiv.org/abs/2201.04554), [arXiv:2101.04698](https://arxiv.org/abs/2101.04698)).
- See also: T359, T361, T355

### T359 Iterative absorption
`prove` `find` · stage: argue · signals: set-family, construction
aka: vortex sets, F-designs, hypergraph decompositions, existence of designs
- What: absorb in a sequence of shrinking vortex sets so each leftover is handled at a smaller scale.
- Fits when: decompositions into copies of a fixed hypergraph.
- Lean: —
- Example: existence of F-designs for every hypergraph F, and a new proof of the existence of designs ([arXiv:1611.06827](https://arxiv.org/abs/1611.06827)).
- See also: T358, T360

### T360 Randomized algebraic construction
`find` `prove` · stage: construct · signals: set-family, construction
aka: Keevash's method, existence conjecture for designs, Steiner systems, absorbing templates, divisibility conditions
- What: start from a random piece of an algebraic design, then correct by absorbing templates.
- Fits when: exact combinatorial designs whose divisibility conditions are the only obstruction.
- Lean: —
- Example: Keevash's proof of the existence conjecture for designs (Steiner, 1853) ([arXiv:1401.3665](https://arxiv.org/abs/1401.3665)).
- See also: T359, T437, T440

### T361 Rödl nibble
`find` `bound` · stage: construct · signals: set-family, random, construction
aka: semi-random method, nibble, Erdős–Hanani conjecture, asymptotic Steiner systems, near-perfect matchings, packings, hypergraph colourings
- What: build the object in many small random bites, keeping the remainder pseudorandom.
- Fits when: near-perfect matchings, packings, colourings in hypergraphs with regular degrees.
- Lean: —
- Example: Rödl's proof of the Erdős–Hanani conjecture on asymptotic Steiner systems ([Wikipedia: Rödl nibble](https://en.wikipedia.org/wiki/Rödl_nibble)).
- See also: T362, T358

### T362 Random greedy processes and the differential equations method
`find` `bound` · stage: construct · signals: graph, random, construction, asymptotic
aka: differential equations method, dynamic concentration, random greedy processes with dynamic concentration, triangle-free process, R(3,k) lower bound, Bohman–Keevash
- What: run a random greedy algorithm and track key statistics by ODE approximations with martingale concentration.
- Fits when: lower bounds via constructions too irregular for algebra.
- Lean: —
- Example: the triangle-free process giving R(3,k) ≥ (1/4 - o(1))k²/log k ([arXiv:1302.6279](https://arxiv.org/abs/1302.6279), [arXiv:1302.5963](https://arxiv.org/abs/1302.5963)).
- See also: T361, T383, T376

### T363 Spread measures
`prove` `bound` · stage: argue · signals: set-family, random, threshold
aka: Kahn–Kalai expectation-threshold conjecture, Park–Pham theorem, fractional expectation threshold, spread lemma, robust sunflowers, ALWZ, sunflower bound, thresholds for spanning structures
- What: a measure that does not concentrate on any small sub-configuration forces a random set to contain a full configuration.
- Fits when: thresholds for spanning structures, sunflower-type problems.
- Lean: —
- Example: the Park–Pham proof of the Kahn–Kalai expectation-threshold conjecture; the Alweiss–Lovett–Wu–Zhang sunflower bound ([arXiv:2203.17207](https://arxiv.org/abs/2203.17207), [arXiv:1910.13433](https://arxiv.org/abs/1910.13433), [arXiv:1908.08483](https://arxiv.org/abs/1908.08483)).
- See also: T370, T357

### T364 Entropy method
`bound` `prove` · stage: argue · signals: set-family, inequality, product-structure
aka: entropy counting, entropy and information, entropic strengthening, Shearer's lemma, Shearer's inequality, subadditivity of entropy, chain rule, Brégman's theorem, permanents, union-closed sets conjecture, Frankl's conjecture, homomorphism counts
- What: bound counts by the entropy of a uniform random object; subadditivity and Shearer's lemma split it into local (projected) pieces.
- Fits when: upper bounds on numbers of configurations, homomorphisms, permutations.
- Lean: a grep finds no Shannon entropy of random variables in Mathlib (it has `Real.negMulLog` and KL divergence in `InformationTheory/KullbackLeibler`); the PFR project develops entropy in Lean 4 ([PFR](https://teorth.github.io/pfr/)).
- Example: Radhakrishnan's entropy proof of Brégman's permanent bound, in Galvin's lectures; Gilmer's constant bound for the union-closed sets conjecture via H(A ∪ B) > H(A) ([arXiv:1406.7872](https://arxiv.org/abs/1406.7872), [arXiv:2211.09055](https://arxiv.org/abs/2211.09055)); Shearer's inequality ([Wikipedia: Shearer's inequality](https://en.wikipedia.org/wiki/Shearer's_inequality)).
- See also: T612, T421, T795, T373

### T365 Graph limits
`prove` `bound` · stage: reformulate · signals: graph, dense, asymptotic
aka: graphons, homomorphism densities, cut distance, dense graph limits, queenons, n-queens counting
- What: pass to a limit object of a convergent graph sequence and solve an analytic optimization there.
- Fits when: asymptotic densities of subgraphs, or extremal problems in the dense limit.
- Lean: —
- Example: homomorphism densities and quasirandomness via graphons; Simkin's "queenons" for counting n-queens configurations ([Wikipedia: Graphon](https://en.wikipedia.org/wiki/Graphon), [arXiv:2107.13460](https://arxiv.org/abs/2107.13460)).
- See also: T55, T368, T373

### T366 Algebraic constructions
`find` `bound` · stage: construct · signals: graph, finite-field, construction
aka: norm graphs, projective norm graphs, polarity graphs, Kollár–Rónyai–Szabó, bipartite Turán numbers, Zarankiewicz problem, K_{s,t}-free graphs
- What: vertices are points of a finite field structure, edges defined by an equation that rules out the forbidden subgraph.
- Fits when: lower bounds for bipartite Turán numbers, where random graphs are far from optimal.
- Lean: Mathlib has `GaloisField` and `ZMod p`; a small instance by `decide +kernel`.
- Example: Kollár–Rónyai–Szabó norm graphs showing ex(n, K_{s,t}) = Θ(n^{2-1/s}) for t > s! ([Wikipedia: Zarankiewicz problem](https://en.wikipedia.org/wiki/Zarankiewicz_problem)).
- See also: T367, T388, T434

### T367 Random algebraic construction
`find` `bound` · stage: construct · signals: graph, polynomial, random, construction
aka: Bukh's construction, random polynomials as edge relations, rational Turán exponents, Bukh–Conlon, K_{s,t}-free graphs
- What: take a random polynomial of bounded degree as the edge relation; algebraic rigidity gives "non-smooth" distributions with few bad configurations.
- Fits when: the extremal number is believed polynomial with rational exponent.
- Lean: —
- Example: Bukh's construction for K_{s,t}; Bukh–Conlon showing every rational in (1,2) is a Turán exponent of some family ([arXiv:1409.3856](https://arxiv.org/abs/1409.3856), [arXiv:1506.06406](https://arxiv.org/abs/1506.06406)).
- See also: T366, T388

### T368 Quasirandomness equivalences
`prove` · stage: argue · signals: graph, pseudorandom, matrix
aka: Chung–Graham–Wilson theorem, quasirandom graphs, 4-cycle count, eigenvalue condition, edge distribution, diagonal Ramsey upper bound
- What: many random-like properties (edge distribution, 4-cycle count, eigenvalues) are equivalent; check the easiest one.
- Fits when: proving that an explicit graph or set behaves randomly.
- Lean: —
- Example: Chung–Graham–Wilson quasirandom graphs; Conlon's diagonal Ramsey upper bound via quasirandomness counting ([Wikipedia: Quasi-random graph](https://en.wikipedia.org/wiki/Quasi-random_graph), [arXiv:math/0607788](https://arxiv.org/abs/math/0607788)).
- See also: T402, T365, T407

### T369 Katona's circle method
`prove` `bound` · stage: argue · signals: set-family, symmetric, inequality
aka: cyclic orderings, averaging over permutations, intersecting families, Erdős–Ko–Rado theorem
- What: average over cyclic orderings; in each, few sets of the family can be intervals.
- Fits when: intersecting families of k-sets.
- Lean: Mathlib: `Combinatorics/KatonaCircle.lean`; Erdős–Ko–Rado is `Finset.erdos_ko_rado`.
- Example: Katona's short proof of the Erdős–Ko–Rado theorem ([Wikipedia: Erdős–Ko–Rado theorem](https://en.wikipedia.org/wiki/Erdős–Ko–Rado_theorem)).
- See also: T349, T347, T327

### T370 Sunflower lemma
`prove` `bound` · stage: argue · signals: set-family, logic
aka: Δ-system lemma, Erdős–Rado sunflower lemma, sunflower conjecture, circuit lower bounds, set-system Ramsey problems
- What: large uniform families contain sunflowers; iterate to find structure.
- Fits when: circuit lower bounds, set-system Ramsey problems, Δ-system arguments in set theory.
- Lean: a grep finds no sunflower or Δ-system lemma in Mathlib.
- Example: Erdős–Rado sunflower lemma and its 2019 improvement ([Wikipedia: Sunflower](https://en.wikipedia.org/wiki/Sunflower_%28mathematics%29), [arXiv:1908.08483](https://arxiv.org/abs/1908.08483)).
- See also: T363, T436

### T371 VC dimension and Sauer–Shelah
`prove` `bound` · stage: argue · signals: set-family, geometry
aka: Vapnik–Chervonenkis dimension, shattering, Sauer–Shelah lemma, traces, ε-nets, bounded-complexity set systems
- What: bounded shattering implies polynomial growth of traces, small ε-nets, and regularity with few parts.
- Fits when: set systems from geometry or bounded-complexity definitions.
- Lean: Mathlib: `Finset.Shatters`, `Finset.vcDim`, `Finset.card_shatterer_le_sum_vcDim` (`Combinatorics/SetFamily/Shatter.lean`).
- Example: Sauer–Shelah lemma; ε-nets of size O((d/ε) log(1/ε)) ([Wikipedia: Sauer–Shelah lemma](https://en.wikipedia.org/wiki/Sauer–Shelah_lemma), [Wikipedia: ε-net (computational geometry)](https://en.wikipedia.org/wiki/Ε-net_%28computational_geometry%29)).
- See also: T740, T758, T398

### T372 Correlation inequalities
`prove` `bound` · stage: argue · signals: set-family, random, order, inequality
aka: Harris inequality, FKG inequality, Kleitman's lemma, Holley inequality, Ahlswede–Daykin four functions theorem, monotone events, distributive lattices, percolation
- What: increasing events are positively correlated on product spaces and distributive lattices.
- Fits when: lower-bounding probabilities of intersections of monotone events.
- Lean: Mathlib: `four_functions_theorem`, `holley`, `fkg` (`Combinatorics/SetFamily/FourFunctions.lean`); Harris–Kleitman in `Combinatorics/SetFamily/HarrisKleitman.lean`.
- Example: Harris's inequality, found in his study of planar percolation; FKG in random graphs ([Wikipedia: FKG inequality](https://en.wikipedia.org/wiki/FKG_inequality)).
- See also: T794, T382

### T373 Homomorphism-density inequalities
`prove` `bound` · stage: argue · signals: graph, inequality, dense
aka: Sidorenko's conjecture, Sidorenko-type inequalities, bipartite pattern densities, Cauchy–Schwarz, tensor powers, entropy, trees, even cycles, hypercubes
- What: prove H-density ≥ edge-density^{e(H)} by Cauchy–Schwarz, tensor powers or entropy.
- Fits when: counting bipartite patterns.
- Lean: —
- Example: known cases of Sidorenko's conjecture (trees, even cycles, hypercubes) ([Wikipedia: Sidorenko's conjecture](https://en.wikipedia.org/wiki/Sidorenko's_conjecture)).
- See also: T365, T364, T622, T606

### T842 Forbidden submatrix patterns (Füredi–Hajnal, Marcus–Tardos)
`prove` `bound` · stage: argue · signals: matrix, order, asymptotic
aka: extremal functions of 0-1 matrices, f(n, P), ex(n, P), forbidden submatrices, excluded permutation matrices, pattern avoidance, Füredi–Hajnal conjecture, Marcus–Tardos theorem, Stanley–Wilf conjecture, Klazar's reduction, block contraction
- What: bounds the number of ones in an n × n 0-1 matrix avoiding a fixed pattern P; for a k × k permutation matrix, cut into blocks of side a = k², bound by pigeonhole the blocks with ones in at least k rows or columns, and recurse on the contracted matrix: f(n) ≤ (k−1)² f(n/a) + 2ak·C(a, k)·n, so f(n, P) = O(n).
- Fits when: a counting or extremal question about permutations, orders or sequences encodes as a 0-1 matrix avoiding a pattern; a reduction like Klazar's can turn the linear bound into an exponential count.
- Lean: not in Mathlib; the proof is pigeonhole plus a recursion on block matrices, a feasible formalization; small values of f(n, P) by exhaustive search with the extremal matrix as witness (T118).
- Example: Marcus–Tardos proved a linear bound for every permutation matrix, settling Füredi–Hajnal and, by Klazar's reduction, the Stanley–Wilf conjecture ([Marcus–Tardos, JCTA 2004](https://doi.org/10.1016/j.jcta.2004.04.002), [Wikipedia: Stanley–Wilf conjecture](https://en.wikipedia.org/wiki/Stanley%E2%80%93Wilf_conjecture)); Zeilberger's one-page rendition gives the block recursion ([Zeilberger](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/martar.html)); Fox showed the resulting Stanley–Wilf limits are typically exponential in k ([arXiv:1310.8378](https://arxiv.org/abs/1310.8378)).
- See also: T304, T325, T320
