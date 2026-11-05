# Communication complexity
Lower bounds on the bits two or more parties must exchange, and their uses for circuits, LPs and matrices.

### T1032 Fooling sets and rectangles
`bound` · stage: argue · signals: matrix, set-family, resource-bound
aka: monochromatic rectangles, fooling set, rectangle partition, communication matrix, equality function, deterministic communication, covers of 0/1 matrices
- What: a protocol partitions the communication matrix into monochromatic rectangles; inputs that no rectangle can share force cost.
- Fits when: quick lower bounds; also bounds the size of covers or partitions of a 0/1 matrix.
- Lean: a fooling set of a fixed matrix by `decide`.
- Example: equality needs n bits ([Wikipedia: Communication complexity](https://en.wikipedia.org/wiki/Communication_complexity)).
- See also: T1033, T1016

### T1033 Rank method and the log-rank conjecture
`bound` · stage: argue · signals: matrix, graph, colouring, resource-bound
aka: log-rank conjecture, rank lower bound, Lovett, low-rank matrices, adjacency rank, chromatic number of low-rank graphs
- What: communication cost is at least log rank; protocols bounded in terms of rank give upper bounds.
- Fits when: matrix-structured problems; also colouring graphs of low adjacency rank.
- Lean: —
- Example: O(√r·log r) protocols, so graphs of adjacency rank r have chromatic number 2^{O(√r log r)} ([Lovett](https://arxiv.org/abs/1306.1877)).
- See also: T1032

### T1034 Distributional and corruption bounds
`bound` · stage: argue · signals: matrix, random, resource-bound
aka: corruption bound, hard distribution, randomized communication, set disjointness, Razborov, large rectangles must err
- What: a hard input distribution under which every large rectangle must err.
- Fits when: randomized lower bounds.
- Lean: —
- Example: Razborov's Ω(n) for set disjointness ([Wikipedia: Communication complexity](https://en.wikipedia.org/wiki/Communication_complexity)).
- See also: T1030, T1035

### T1035 Information complexity
`bound` `compute` · stage: argue · signals: product-structure, exact-value, resource-bound
aka: information cost, IC, direct sum, amortized communication, exact constants, set disjointness constant, IC(AND), Braverman
- What: measures the information a protocol reveals; it adds up across independent copies.
- Fits when: direct-sum questions and exact constants.
- Lean: —
- Example: IC equals amortized communication ([Braverman](https://eccc.weizmann.ac.il/report/2011/123/)); randomized disjointness costs ≈ 0.4827n, from IC(AND) ≈ 1.4923 bits ([Braverman–Garg–Pankratov–Weinstein](https://eccc.weizmann.ac.il/report/2012/171)).
- See also: T1034

### T1036 Karchmer–Wigderson games
`bound` · stage: reformulate · signals: computation, game, resource-bound
aka: KW games, circuit depth, formula size, monotone circuits, monotone depth, st-connectivity, matching, find a differing coordinate
- What: the circuit depth of f equals the communication cost of finding a coordinate where an input with f = 1 and one with f = 0 differ.
- Fits when: depth or formula lower bounds, monotone circuits.
- Lean: —
- Example: Ω(log² n) monotone depth for st-connectivity, Ω(n) for matching ([Raz lecture notes](https://www.cs.princeton.edu/courses/archive/spring19/cos522/KW.pdf)).
- See also: T1041, T1037

### T1037 Lifting theorems
`bound` · stage: reformulate · signals: computation, resource-bound
aka: query-to-communication lifting, gadget composition, decision-tree to communication, partition number, Clique vs Independent Set, Göös–Pitassi–Watson
- What: composes with a gadget so that query lower bounds become communication lower bounds.
- Fits when: a decision-tree bound is provable but a communication or extension bound is needed.
- Lean: —
- Example: deterministic communication superlogarithmic in the partition number; near-optimal bounds for Clique vs Independent Set ([Göös–Pitassi–Watson](https://eccc.weizmann.ac.il/report/2015/050/)).
- See also: T1024, T1016

### T1038 Pattern matrix and dual polynomial method
`bound` · stage: argue · signals: matrix, polynomial, resource-bound
aka: Sherstov, pattern matrices, approximate degree, dual polynomials, quantum communication, degree to communication
- What: the approximate degree of f lower-bounds the communication cost of a derived pattern matrix.
- Fits when: converting polynomial-degree bounds into communication bounds.
- Lean: —
- Example: Ω(d) for pattern matrices, even for quantum protocols ([Sherstov](https://arxiv.org/abs/0906.4291)).
- See also: T1028

### T1039 Number-on-forehead protocols with additive combinatorics
`bound` · stage: argue · signals: additive, computation, resource-bound
aka: NOF, multiparty communication, three-party protocols, corners, 3-AP density, Kelley–Meka, randomized versus deterministic separation
- What: proves three-party number-on-forehead bounds through corner and 3-AP density arguments.
- Fits when: problems that mix additive structure with multiparty protocols.
- Lean: —
- Example: an explicit separation of randomized and deterministic NOF communication, extending Kelley–Meka ([Kelley–Lovett–Meka](https://arxiv.org/abs/2308.12451)).
- See also: T1034
