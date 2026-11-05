# Counting and dynamic programming
Exact counting and optimization algorithms: subset DP, transforms over subsets, algebraic sieving, transfer matrices, decision diagrams, convolution, approximate counting.

### T1112 Subset dynamic programming
`compute` `find` · stage: search · signals: graph, exact-value
aka: Held–Karp, DP over subsets, bitmask DP, travelling salesman, Hamiltonian paths, n·2ⁿ memory, n up to about 30
- What: tabulates over subsets and endpoints.
- Fits when: exact optimization or counting with n up to about 30 on one PC (n·2ⁿ memory).
- Lean: an optimum's witness by `decide`; the optimum or count itself needs a verified DP run in the kernel (T120), feasible only for small n.
- Example: Held–Karp TSP in Θ(2ⁿn²) ([Wikipedia: Held–Karp algorithm](https://en.wikipedia.org/wiki/Held%E2%80%93Karp_algorithm)).
- See also: T1113, T1114

### T1113 Inclusion–exclusion with the zeta transform
`compute` · stage: search · signals: set-family, colouring, exact-value
aka: zeta transform, set partitioning, set covers, counting covers, chromatic number in 2ⁿ time, chromatic polynomial, Björklund–Husfeldt–Koivisto
- What: counts covers or partitions by an alternating sum over subsets, tabulated with a fast zeta transform.
- Fits when: chromatic number, chromatic polynomial, partitions and covers in 2ⁿ time.
- Lean: Mathlib has inclusion–exclusion (`Finset.inclusion_exclusion_card_biUnion`); the numbers need a kernel-run evaluation (T120).
- Example: set partitioning in 2ⁿn^{O(1)} time ([Björklund–Husfeldt–Koivisto](https://www.cs.helsinki.fi/u/mkhkoivi/publications/sicomp-2009.pdf)).
- See also: T1009, T1114, T1121

### T1114 Fast subset convolution
`compute` · stage: search · signals: set-family, exact-value
aka: subset convolution, ranked zeta transform, Möbius transform, O(n²2ⁿ), Steiner trees, partitions, combining disjoint parts
- What: subset convolution in O(n²2ⁿ) via ranked zeta and Möbius transforms.
- Fits when: DP that combines disjoint parts (Steiner trees, partitions).
- Lean: as for T1113.
- Example: [Björklund–Husfeldt–Kaski–Koivisto](https://arxiv.org/abs/cs/0611101).
- See also: T1113

### T1115 Determinant sums
`find` `prove` · stage: search · signals: graph, finite-field
aka: algebraic sieving, characteristic 2, cancellation of non-solutions, Hamiltonicity, Hamiltonian cycles, O*(1.657ⁿ), Monte Carlo, Björklund
- What: sums determinants over a field of characteristic 2 so that non-solutions cancel.
- Fits when: detecting Hamiltonicity, paths or covers faster than 2ⁿ (Monte Carlo).
- Lean: a found cycle by `decide`; a negative Monte Carlo answer proves nothing.
- Example: undirected Hamiltonicity in O*(1.657ⁿ) ([Björklund](https://arxiv.org/abs/1008.0541)).
- See also: T1116, T1070

### T1116 Multilinear monomial detection
`find` · stage: search · signals: graph, polynomial
aka: group algebras, k-path, O*(2^k), Williams, packing, subgraph detection, parameterized by k
- What: detects a multilinear term in a polynomial via group algebras.
- Fits when: k-path, packing and subgraph detection parameterized by k.
- Lean: a found pattern by `decide`.
- Example: k-paths in O*(2^k) ([Williams](https://arxiv.org/abs/0807.3026)).
- See also: T1126, T1115

### T1117 Transfer-matrix method
`compute` · stage: search · signals: geometry, sequence, exact-value
aka: finite-lattice method, frontier sweep, boundary states, strips, polyominoes, tilings, self-avoiding walks, grid enumeration, Jensen–Guttmann
- What: sweeps a frontier across a strip, keeping the states of the boundary.
- Fits when: enumeration on grids (polyominoes, tilings, self-avoiding walks).
- Lean: small terms by a verified sweep run in the kernel (T120); record-size terms do not fit.
- Example: polyominoes counted to size 46 ([Jensen–Guttmann](https://arxiv.org/abs/cond-mat/0007238)).
- See also: T1118, T62

### T1118 Frontier-based search into decision diagrams
`compute` · stage: search · signals: graph, exact-value
aka: BDD, ZDD, zero-suppressed decision diagrams, frontier-based search, compressed solution sets, counting paths, trees and partitions, corner-to-corner paths on grids
- What: builds a compressed diagram of all solutions, then counts or optimizes on it.
- Fits when: counting constrained subgraphs (paths, trees, partitions) far beyond explicit listing.
- Lean: as for T1117.
- Example: the framework ([Kawahara–Inoue–Iwashita–Minato](https://www.jstage.jst.go.jp/article/transfun/E100.A/9/E100.A_1773/_article/-char/en)); 789,360,053,252 corner-to-corner paths on an 8×8 grid ([Wikipedia: Zero-suppressed decision diagram](https://en.wikipedia.org/wiki/Zero-suppressed_decision_diagram)).
- See also: T12, T1117

### T1119 Holographic reductions
`compute` · stage: algebra · signals: graph, exact-value, congruence
aka: holographic algorithms, Valiant, many-to-many reductions, planar perfect matchings, cancellations, counting mod 7, #₇Pl-Rtw-Mon-3CNF, computer-found reductions
- What: many-to-many reductions to planar perfect matchings, with cancellations; found by computer search.
- Fits when: exotic counting problems that look #P-hard.
- Lean: —
- Example: Valiant's #₇Pl-Rtw-Mon-3CNF (counting mod 7) ([Wikipedia: Holographic algorithm](https://en.wikipedia.org/wiki/Holographic_algorithm)).
- See also: T1008

### T1120 FFT and number-theoretic transform convolution
`compute` · stage: algebra · signals: additive, polynomial, exact-value
aka: fast Fourier transform, NTT, number-theoretic transform, Cooley–Tukey, exact convolution over finite fields, sumset counting, representation numbers, polynomial multiplication
- What: convolutions in O(n log n), exact over finite fields with the NTT.
- Fits when: counting sumsets, representation numbers and polynomial products in compute runs.
- Lean: — (the counts need their own kernel check; small cases by direct `decide`)
- Example: Cooley–Tukey 1965 and NTT variants ([Wikipedia: Fast Fourier transform](https://en.wikipedia.org/wiki/Fast_Fourier_transform)).
- See also: T121

### T1121 Gray-code enumeration
`compute` · stage: search · signals: set-family, exact-value
aka: Gray code, one-element changes, O(1) updates per step, Ryser's formula, permanent, inclusion–exclusion sums, sums over all subsets
- What: visits all subsets so that consecutive ones differ in one element, making each step an O(1) update.
- Fits when: exhaustive sums over subsets, inclusion–exclusion.
- Lean: —
- Example: Ryser's permanent formula in Gray-code order runs in O(2ⁿn) ([Wikipedia: Computing the permanent](https://en.wikipedia.org/wiki/Computing_the_permanent); [Wikipedia: Gray code](https://en.wikipedia.org/wiki/Gray_code)).
- See also: T1113

### T1122 Polynomial method in algorithm design
`compute` · stage: search · signals: polynomial, matrix
aka: probabilistic polynomials, batch evaluation, fast matrix multiplication, all-pairs shortest paths, APSP, n³/2^{Ω(√log n)}, Williams, inner-loop speedups
- What: encodes a comparison or predicate as a probabilistic low-degree polynomial, then batches the evaluations with fast matrix multiplication.
- Fits when: speeding up all-pairs or inner-loop computations in compute runs.
- Lean: —
- Example: APSP in n³/2^{Ω(√log n)} ([Williams](https://arxiv.org/abs/1312.6680)).
- See also: T1045, T1005

### T1123 MCMC approximate counting
`compute` · stage: explore · signals: random, matrix
aka: Markov chain Monte Carlo, rapid mixing, FPRAS, approximate counting, permanent of non-negative matrices, Jerrum–Sinclair–Vigoda, estimating solution-space size
- What: rapidly mixing Markov chains give fully polynomial randomized approximation schemes for #P-hard counts.
- Fits when: estimating the size of a solution space before an exact run (not a proof).
- Lean: —
- Example: the permanent of non-negative matrices ([Jerrum–Sinclair–Vigoda](https://eccc.weizmann.ac.il/report/2000/079/)).
- See also: T1102, T1075, T1332
