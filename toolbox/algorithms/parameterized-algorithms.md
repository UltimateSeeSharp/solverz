# Parameterized and exact exponential algorithms
Kernels, compression, colour coding, width-based DP and branching analysis, used as structure detectors and preprocessors.

### T1124 Kernelization
`compute` `find` · stage: search · signals: graph
aka: reduction rules, problem kernel, Buss kernel, crown reduction, LP kernel, vertex cover, preprocessing, hard core of an instance
- What: polynomial-time reduction rules shrink an instance to size f(k); what remains is the hard core.
- Fits when: preprocessing before exact search; the kernel shows which structure matters.
- Lean: prove each reduction rule sound once; the kernel instance then needs its own certificate.
- Example: Buss's k² kernel and the crown and LP 2k kernels for vertex cover ([Wikipedia: Kernelization](https://en.wikipedia.org/wiki/Kernelization)).
- See also: T1077, T1007

### T1125 Iterative compression
`find` `compute` · stage: search · signals: graph
aka: compress a size-(k+1) solution to size k, add one element at a time, deletion problems, odd cycle transversal, feedback vertex set, Reed–Smith–Vetta
- What: adds one element at a time and compresses a size-(k+1) solution to size k.
- Fits when: deletion problems (odd cycle transversal, feedback vertex set).
- Lean: a found solution by `decide`.
- Example: Reed–Smith–Vetta odd cycle transversal in O(3^k·kmn) ([Wikipedia: Iterative compression](https://en.wikipedia.org/wiki/Iterative_compression)).
- See also: T1124

### T1126 Colour coding
`find` · stage: search · signals: graph, random
aka: Alon–Yuster–Zwick, colourful paths, random colourings, k-paths, cycles, bounded-treewidth patterns, dynamic programming
- What: a random colouring makes the sought pattern colourful; dynamic programming then finds it.
- Fits when: finding small paths, cycles or bounded-treewidth patterns.
- Lean: a found pattern by `decide`.
- Example: Alon–Yuster–Zwick 1994 ([Wikipedia: Color-coding](https://en.wikipedia.org/wiki/Color-coding)).
- See also: T1116

### T1127 Treewidth and treedepth solvers
`compute` · stage: search · signals: graph, sparse
aka: PACE challenge, tree decompositions, treedepth, exact and heuristic decompositions, exploitable width, competition solvers
- What: exact or heuristic decompositions from competition-grade codes.
- Fits when: testing whether an instance has exploitable width before DP.
- Lean: a decomposition is a finite witness, checked by `decide`.
- Example: PACE challenge tracks ([PACE](https://pacechallenge.org/)).
- See also: T1128

### T1128 DP over tree decompositions (Courcelle)
`compute` `prove` · stage: search · signals: graph, logic, sparse
aka: Courcelle's theorem, monadic second-order logic, MSO properties, bounded treewidth, linear time, counting versions
- What: MSO-definable properties are decidable in linear time on graphs of bounded treewidth, and counting versions too.
- Fits when: instances with small treewidth.
- Lean: —
- Example: [Wikipedia: Courcelle's theorem](https://en.wikipedia.org/wiki/Courcelle%27s_theorem).
- See also: T1127, T1008

### T1129 Measure and conquer
`compute` · stage: search · signals: graph, resource-bound
aka: branch-and-reduce analysis, weighted measures, exponential running-time bounds, tuning branching rules, Fomin–Grandoni–Kratsch, dominating set, independent set
- What: analyses a branching algorithm with a weighted measure chosen by optimization.
- Fits when: proving exponential running-time bounds, or tuning the branching rules of your own search.
- Lean: —
- Example: Nerode Prize laudation for Fomin–Grandoni–Kratsch (dominating set, independent set) ([EATCS](https://eatcs.org/index.php/component/content/article/1-news/2633-ipec-nerode-prize-2017-laudatio)).
- See also: T1102
