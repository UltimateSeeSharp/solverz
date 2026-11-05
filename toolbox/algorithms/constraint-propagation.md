# Constraint propagation
Filtering inside CP and subgraph solvers: arc consistency, matching-based alldifferent, table constraints, lazy clause generation, invariant filtering.

### T1107 Arc consistency (AC-3)
`find` `compute` · stage: search · signals: local-constraints
aka: AC-3, Mackworth, binary constraints, supports, domain filtering, CSP propagation, baseline propagation
- What: deletes values with no support in a binary constraint and re-queues the affected arcs.
- Fits when: any CSP model; baseline propagation.
- Lean: a solution by `decide`; non-existence needs a logged proof (T25).
- Example: Mackworth 1977 ([Wikipedia: AC-3 algorithm](https://en.wikipedia.org/wiki/AC-3_algorithm)).
- See also: T14, T1108

### T1108 Alldifferent by matching
`find` `compute` · stage: search · signals: graph, order, local-constraints
aka: global constraints, alldifferent, generalized arc consistency, GAC, maximum matching, strongly connected components, Régin, permutations, Latin squares, injective maps, subgraph isomorphism, RESYN
- What: generalized arc consistency for alldifferent, from a maximum matching and strongly connected components.
- Fits when: permutation, Latin or injective-map structure.
- Lean: a solution by `decide`; non-existence needs a logged proof (T25).
- Example: used for subgraph isomorphism in RESYN ([Régin 1994](https://mlanthology.org/aaai/1994/regin1994aaai-filtering)).
- See also: T14, T1081

### T1109 Table constraints
`find` `compute` · stage: search · signals: local-constraints
aka: extensional constraints, allowed tuples, table propagation, bipartite encoding, GAC solvers, small gadgets, local patterns
- What: propagates constraints given as lists of allowed tuples.
- Fits when: constraints given as tables (small gadgets, local patterns).
- Lean: a solution by `decide`; non-existence needs a logged proof (T25).
- Example: a bipartite encoding beats GAC solvers on table benchmarks ([Wang–Yap](https://www.ijcai.org/proceedings/2020/165)).
- See also: T14

### T1110 Lazy clause generation
`find` `compute` · stage: search · signals: local-constraints
aka: LCG, propagators emit clauses, nogood learning, conflict learning with global constraints, CP-SAT, OR-Tools, arithmetic constraints
- What: propagators emit clauses on demand, so a SAT core learns nogoods.
- Fits when: CP problems with arithmetic or global constraints that also need conflict learning (CP-SAT style).
- Lean: as for T14.
- Example: [Ohrimenko–Stuckey–Codish](https://findanexpert.unimelb.edu.au/scholarlywork/314218-propagation-via-lazy-clause-generation); [OR-Tools CP-SAT](https://developers.google.com/optimization/cp/cp_solver).
- See also: T1, T14

### T1111 Graph-invariant filtering for subgraph search
`find` `prove` · stage: search · signals: graph, local-constraints
aka: subgraph isomorphism, Glasgow Subgraph Solver, degree filtering, neighbourhood degree sequences, path counts, pattern-to-target maps, proof logging, VeriPB, Ramsey and extension problems
- What: prunes pattern-to-target maps by invariants (degrees, neighbourhood degree sequences, path counts).
- Fits when: subgraph search inside Ramsey or extension problems, with proof logging.
- Lean: an embedding by `decide`; non-existence via VeriPB proofs, which need a kernel checker (T25).
- Example: the Glasgow Subgraph Solver, MIT licence, with VeriPB proof logging ([GitHub](https://github.com/ciaranm/glasgow-subgraph-solver)).
- See also: T25, T1090
