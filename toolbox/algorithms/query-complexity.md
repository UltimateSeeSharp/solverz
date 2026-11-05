# Query and decision-tree complexity
Lower and exact bounds on how many probes, comparisons or queries any algorithm needs.

### T1024 Adversary argument
`bound` `prove` · stage: argue · signals: computation, graph, resource-bound
aka: adversary strategy, evasiveness, evasive properties, monotone graph properties, Rivest–Vuillemin, Aanderaa–Karp–Rosenberg conjecture, probe lower bounds, search-tree depth
- What: answers queries so that the outcome stays undetermined as long as possible.
- Fits when: lower bounds on how many probes or checks any algorithm needs; also bounds search-tree depth.
- Lean: for fixed small n, exact query counts by search (T1026); in general a by-hand proof.
- Example: Rivest–Vuillemin's Ω(n²) for nontrivial monotone graph properties ([Wikipedia: Aanderaa–Karp–Rosenberg conjecture](https://en.wikipedia.org/wiki/Aanderaa%E2%80%93Karp%E2%80%93Rosenberg_conjecture)).
- See also: T1030, T1031

### T1025 Information-theoretic leaf-counting bound
`bound` `compute` · stage: argue · signals: order, inequality, resource-bound
aka: decision-tree lower bound, log₂ N, ⌈log₂ n!⌉, comparison sorting, information-theoretic lower bound, counting outcomes, minimum comparisons, minimum queries
- What: a decision tree with N outcomes has depth at least log₂ N.
- Fits when: the first sanity bound for any problem about minimum comparisons or queries.
- Lean: for fixed n, the bound ⌈log₂ N⌉ by `decide` or `norm_num`.
- Example: comparison sorting needs ⌈log₂ n!⌉ comparisons ([Wikipedia: Decision tree model](https://en.wikipedia.org/wiki/Decision_tree_model)).
- See also: T1026

### T1026 Exhaustive search over decision trees
`compute` `bound` · stage: search · signals: order, exact-value, resource-bound
aka: S(n), minimum comparisons for sorting, partial-order states, state canonicalization, bidirectional search, search from both ends, Knuth's S(16)=45 disproved, optimal query counts
- What: computes exact optimal query counts by searching over partial-order states, from both ends (bidirectional search), with states canonicalized.
- Fits when: compute or bound problems on S(n)-type minima, and other exact minima where start and goal are both structured.
- Lean: an upper bound is a decision tree checked by `decide` on all inputs; the lower bound needs the search itself as a certificate (T120, T122).
- Example: S(16)=46, S(17)=50 and S(18)=54, disproving Knuth's S(16)=45 ([Stober–Weiß](https://arxiv.org/abs/2206.05597)).
- See also: T36, T1025

### T1027 Complexity-measure relations
`prove` · stage: argue · signals: set-family, graph, inequality, resource-bound
aka: sensitivity, block sensitivity, certificate complexity, polynomial degree, Sensitivity Conjecture, Huang, Boolean function measures, polynomially related measures, induced subgraphs of the hypercube
- What: polynomial relations between measures turn a bound on one into bounds on the others.
- Fits when: proving facts about Boolean functions; pick the measure that is easiest to bound.
- Lean: —
- Example: Huang proved bs(f)=O(s(f)⁴), settling the Sensitivity Conjecture ([Huang](https://arxiv.org/abs/1907.00847); [Wikipedia: Decision tree model](https://en.wikipedia.org/wiki/Decision_tree_model)).
- See also: T1028, T1053

### T1028 Polynomial method for query lower bounds
`bound` `prove` · stage: argue · signals: polynomial, set-family, computation, resource-bound
aka: approximate degree, acceptance polynomial, degree at most 2T, quantum query complexity, randomized query complexity, Beals et al., quantum speedup for total functions
- What: T queries give an acceptance polynomial of degree at most 2T, so lower bounds on (approximate) degree bound the queries.
- Fits when: lower bounds for quantum or randomized query algorithms.
- Lean: —
- Example: total functions admit at most a 6th-power quantum speedup ([Beals et al.](https://arxiv.org/abs/quant-ph/9802049)).
- See also: T1029, T1038

### T1029 Quantum adversary method
`bound` · stage: argue · signals: quantum, computation, resource-bound
aka: spectral adversary, Ambainis, superposition of inputs, quantum query lower bounds, AND of ORs, permutation inversion, Ω(√N)
- What: runs the algorithm on a superposition of inputs and bounds its progress per query.
- Fits when: query lower bounds where the polynomial method is weak.
- Lean: —
- Example: Ω(√N) for AND-of-ORs and for inverting a permutation ([Ambainis](https://arxiv.org/abs/quant-ph/0002066)).
- See also: T1028

### T1030 Yao's minimax principle
`bound` `prove` · stage: argue · signals: computation, game, resource-bound
aka: Yao's principle, games and minimax, hard input distribution, randomized lower bounds, deterministic versus randomized, LP duality, search games, randomized evasiveness, swap quantifiers
- What: lower-bounds randomized algorithms by a hard input distribution against deterministic ones.
- Fits when: any randomized lower bound; also the LP-duality view of a search game.
- Lean: —
- Example: randomized evasiveness of planarity, perfect matching and Hamiltonicity ([Wikipedia: Yao's principle](https://en.wikipedia.org/wiki/Yao%27s_principle)).
- See also: T1024, T1034

### T1031 Topological method for evasiveness
`prove` · stage: argue · signals: topology, graph, symmetric, resource-bound
aka: Kahn–Saks–Sturtevant, fixed-point theorems, simplicial complex of a monotone property, evasive graph properties, prime-power n, Aanderaa–Karp–Rosenberg conjecture
- What: applies fixed-point theorems to the simplicial complex of a monotone property.
- Fits when: symmetric monotone properties; niche but decisive.
- Lean: —
- Example: Kahn–Saks–Sturtevant prove evasiveness for prime-power n ([Wikipedia: Aanderaa–Karp–Rosenberg conjecture](https://en.wikipedia.org/wiki/Aanderaa%E2%80%93Karp%E2%80%93Rosenberg_conjecture)).
- See also: T1024
