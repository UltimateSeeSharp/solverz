# Boolean functions and pseudorandomness
Fourier analysis on the cube, juntas and thresholds, extractors, list decoding, multiplicative weights, weak regularity and spread approximations.

### T1053 Fourier expansion and linearity testing
`prove` · stage: argue · signals: set-family, finite-field
aka: Boolean Fourier analysis, analysis of Boolean functions, parity basis, Walsh expansion, Parseval, BLR linearity test, property testing, sets in the cube, local tests
- What: writes f: {±1}ⁿ → ℝ in the parity basis; Parseval controls distances.
- Fits when: statements about Boolean functions, sets in the cube, or local tests.
- Lean: —
- Example: the BLR linearity test and its Fourier proof ([O'Donnell, Analysis of Boolean Functions](https://arxiv.org/abs/2105.10386)).
- See also: T1054, T1056, T1027

### T1054 Junta theorems
`prove` · stage: argue · signals: set-family, inequality
aka: Friedgut's junta theorem, FKN theorem, Friedgut–Kalai–Naor, dictators, juntas, stability, almost extremal implies structured, low total influence, near-degree-1 functions
- What: low total influence, or Fourier weight near degree 1, forces dependence on few coordinates.
- Fits when: stability results: "almost extremal implies close to a dictator or junta".
- Lean: —
- Example: Friedgut's junta theorem ([O'Donnell](https://arxiv.org/abs/2105.10386)).
- See also: T1053, T1055

### T1055 Global hypercontractivity
`prove` · stage: argue · signals: set-family, sparse, threshold
aka: p-biased hypercontractivity, global functions, small p, sharp thresholds, Bourgain's sharp-threshold theorem, intersecting families, random graphs
- What: hypercontractivity for p-biased functions that are not dominated by small restrictions.
- Fits when: sparse p-biased settings (random graphs, intersecting families) where classical bounds fail.
- Lean: —
- Example: it strengthens Bourgain's sharp-threshold theorem ([Keevash–Lifshitz–Long–Minzer](https://arxiv.org/abs/1906.05568)).
- See also: T1054, T1061

### T1056 Heavy Fourier coefficient search
`find` · stage: explore · signals: set-family, finite-field
aka: Goldreich–Levin algorithm, low-degree learning, large Fourier coefficients, concentrated spectra, learning from queries, hidden linear structure
- What: finds the large Fourier coefficients of a function from queries; functions with concentrated spectra are learnable.
- Fits when: discovering hidden linear structure in data from experiments.
- Lean: — (a found structure is a conjecture to prove)
- Example: the Goldreich–Levin algorithm, O'Donnell §3.5 ([O'Donnell](https://arxiv.org/abs/2105.10386)).
- See also: T1053, T1074

### T1057 Randomness extractors and dispersers
`find` `bound` · stage: construct · signals: graph, colouring, pseudorandom, asymptotic
aka: two-source extractors, dispersers, weak random sources, explicit Ramsey graphs, Chattopadhyay–Zuckerman, Li, near-uniform bits
- What: functions that output near-uniform bits from weak sources; their outputs give explicit Ramsey graphs.
- Fits when: explicit constructions for Ramsey-type find or bound problems (asymptotic, not small-n records).
- Lean: —
- Example: two-source extractors give 2^{(log log N)^{O(1)}}-Ramsey graphs ([Chattopadhyay–Zuckerman](https://eccc.weizmann.ac.il/report/2015/119/)); log^{O(1)} N ([Li 2023](https://eccc.weizmann.ac.il/report/2023/023)).
- See also: T1063, T91

### T1058 List-decodable codes
`prove` · stage: argue · signals: set-family, pseudorandom
aka: list decoding, error-correcting codes, heavily corrupted data, short list of candidates, reconstruction from noisy data, hardness amplification
- What: decodes to a short list of candidates from heavily corrupted data.
- Fits when: reconstruction from noisy partial data; hardness amplification.
- Lean: —
- Example: Vadhan, Pseudorandomness, ch. 5 ([Vadhan](https://people.seas.harvard.edu/~salil/pseudorandomness/)).
- See also: T1064

### T1059 Multiplicative weights and the hardcore lemma
`prove` `bound` · stage: argue · signals: game, pseudorandom
aka: multiplicative weights update, MWU, hardcore lemma, boosting, Arora–Hazan–Kale, approximate LP and SDP solving, game equilibria, regularity-style decompositions
- What: keeps weights over a set and updates them multiplicatively against losses.
- Fits when: boosting, approximate LP and SDP solving, game equilibria, regularity-style decompositions.
- Lean: —
- Example: the meta-algorithm and its applications ([Arora–Hazan–Kale](https://theoryofcomputing.org/articles/v008a006/)).
- See also: T1060, T52

### T1060 Weak regularity (Frieze–Kannan)
`prove` `bound` · stage: argue · signals: graph, matrix, dense
aka: Frieze–Kannan regularity, cut norm, cut decomposition, cut matrices, threshold rank, dense graphs, structure versus randomness, approximation on dense instances
- What: approximates a dense graph in cut norm by O(1/ε²) cut matrices.
- Fits when: structure–randomness decompositions of tractable size; approximation algorithms on dense instances.
- Lean: Mathlib has Szemerédi's regularity lemma (`szemeredi_regularity`); no file mentions Frieze–Kannan or the cut norm.
- Example: a regularity lemma for low threshold-rank graphs, modelled on Frieze–Kannan ([Oveis Gharan–Trevisan](https://theoryofcomputing.org/articles/v011a009/)).
- See also: T1059, T55

### T1061 Spread approximations
`prove` · stage: argue · signals: set-family, order, inequality
aka: spread families, spread cores, Erdős–Ko–Rado, forbidden intersections, intersecting families of permutations, Kupavskii–Zakharov, growing parameters
- What: replaces an extremal family by a small spread "core" and analyses the core.
- Fits when: Erdős–Ko–Rado and forbidden-intersection problems with growing parameters.
- Lean: —
- Example: the forbidden-intersection theorem for permutations up to t ≈ n^{1−ε} ([Kupavskii–Zakharov](https://arxiv.org/abs/2203.13379)).
- See also: T1055
