# Heuristic search for constructions
Rollout, tree-sampling and neighbourhood methods for find and bound problems, beyond the computation area's local search (T90–T100).

### T1139 Nested Monte Carlo search and NRPA
`find` · stage: local-search · signals: sequence, construction
aka: nested rollouts, nested rollout policy adaptation, NRPA, Morpion Solitaire, puzzles, sequences, packings, long sequential constructions, Rosin
- What: nested rollouts that adapt the rollout policy toward the best sequence found.
- Fits when: long sequential constructions (puzzles, sequences, packings).
- Lean: the final object by `decide`.
- Example: a Morpion Solitaire record that beat a 30-year human record ([Rosin](https://www.ijcai.org/Proceedings/11/Papers/115.pdf)).
- See also: T1140, T104

### T1140 Monte Carlo tree search (UCT)
`find` · stage: local-search · signals: sequence, construction
aka: MCTS, UCT, upper confidence bounds for trees, playouts, AlphaGo, sequential constructions, games without a good heuristic
- What: grows a search tree by sampled playouts, choosing children by upper confidence bounds.
- Fits when: long sequential constructions or games without a good heuristic.
- Lean: the final object by `decide`.
- Example: AlphaGo ([Wikipedia: Monte Carlo tree search](https://en.wikipedia.org/wiki/Monte_Carlo_tree_search)).
- See also: T1139, T104, T1351

### T1141 Large-neighbourhood search
`find` `bound` · stage: local-search · signals: construction, near-miss
aka: LNS, destroy and repair, very large-scale neighbourhood search, VLSN, exact re-optimization of a freed part, CP, ILP or SAT subproblems
- What: frees a large, possibly exponential, part of the current solution and re-optimizes it exactly with CP, ILP or SAT.
- Fits when: local moves stall but an exact solver handles subproblems of a few hundred variables.
- Lean: the final object by `decide`.
- Example: very large-scale neighbourhood search outperforms small neighbourhoods ([Wikipedia: Very large-scale neighborhood search](https://en.wikipedia.org/wiki/Very_large-scale_neighborhood_search)).
- See also: T1, T14, T90

### T1142 Variable neighbourhood search for extremal graphs
`find` `prove` · stage: local-search · signals: graph, inequality, construction
aka: VNS, Mladenović–Hansen, AutoGraphiX, AGX, Digenes, graph invariants, conjectured inequalities between invariants, refuting conjectures, genetic algorithms
- What: changes the neighbourhood structure systematically when stuck; systems built on it search extremal graphs for combinations of invariants and emit conjectures.
- Fits when: conjecturing or refuting inequalities between graph invariants.
- Lean: a counterexample graph and its invariants by `decide`.
- Example: Ilić resolves four AutoGraphiX conjectures, refutes one and corrects another ([arXiv:1106.2987](https://arxiv.org/abs/1106.2987)); VNS is due to Mladenović–Hansen ([Wikipedia: Variable neighborhood search](https://en.wikipedia.org/wiki/Variable_neighborhood_search)); Digenes does the same with genetic algorithms ([arXiv:1304.7993](https://arxiv.org/abs/1304.7993)).
- See also: T80, T93, T101

### T1143 Full-neighbourhood delta evaluation
`find` · stage: local-search · signals: colouring, graph
aka: incremental scoring, delta evaluation, score of every flip, common-neighbourhood counts, cliques through u and v, Exoo, Ramsey colourings
- What: keeps the score change of every single flip and updates only the affected entries.
- Fits when: local search for colourings: flipping edge uv changes only the cliques through u and v.
- Lean: — (speed only; the final colouring is checked as in T91)
- Example: Exoo's search computes all dᵢ = f(Vᵢ) − f(V) at each step ([Exoo 1998](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v5i1r29/pdf)).
- See also: T90, T91
