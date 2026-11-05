# Symmetry reduction and isomorph-free generation
Shrinks a search space by its symmetries, and lists objects once per isomorphism class.

### T24 Static lex-leader symmetry breaking
`find` `prove` `compute` · stage: symmetry · signals: symmetric, colouring, graph
aka: lex-leader predicates, symmetry-breaking clauses, colour symmetry, vertex symmetry, packing chromatic number, grid colouring
- What: adds clauses that keep one representative per symmetry orbit.
- Fits when: large symmetry groups (colours, vertices, coordinates).
- Lean: soundness needs a Lean theorem or a checked redundancy (SR/PR) proof; the Lean 4 Keller proof uses both.
- Example: the packing chromatic number of the grid is 15, found with a new encoding and new symmetry breaking, about 100× faster than before ([Subercaseaux–Heule](https://arxiv.org/abs/2301.09757)).
- See also: T6, T25, T31

### T25 Certified symmetry and dominance breaking
`prove` · stage: certify · signals: symmetric, local-constraints
aka: VeriPB, pb-catcher, PBLean, cutting planes, pseudo-Boolean proof logging, dominance breaking, Glasgow subgraph solver
- What: pseudo-Boolean proof logging that also certifies symmetry and dominance breaking.
- Fits when: symmetry breaking is essential and has to be audited.
- Lean: pb-catcher (formerly PBLean) checks VeriPB proofs in Lean 4 by native evaluation, so it does not count (T127); pins Lean v4.30.0; a kernel-only checker is new work.
- Example: the first efficient proof logging for fully general SAT symmetry breaking ([Bogaerts–Gocht–McCreesh–Nordström](https://arxiv.org/abs/2203.12275); [pb-catcher](https://github.com/leansolving/pblean)).
- See also: T6, T24, T127

### T26 Isomorphism pruning and orbital branching
`bound` `find` · stage: symmetry · signals: symmetric, set-family, construction
aka: ILP branch-and-bound with symmetry handling, isomorphism pruning, orbital branching, covering codes, football pool problem, packing designs, 0/1 programs, Condor
- What: branch-and-bound on a 0/1 program that prunes nodes isomorphic to ones already explored, or branches on orbits of equivalent variables.
- Fits when: covering and packing codes, designs and extremal set problems as 0/1 programs.
- Lean: the primal solution by `decide`; the lower bound needs a tree certificate (T49).
- Example: the football pool problem for v=6, bounded 65 ≤ z ≤ 73: CPLEX stalled at a bound of 58 after 500k nodes, while isomorphism pruning, subcode enumeration and LP bounds on a Condor grid did better ([Linderoth–Margot–Thain](https://jlinderoth.github.io/papers/Linderoth-Margot-Thain-07-TR-1.pdf)).
- See also: T48, T49, T153

### T27 Prescribed automorphism group
`find` · stage: symmetry · signals: symmetric, set-family, graph, construction
aka: Kramer–Mesner method, circulant ansatz, Cayley graphs, block-circulant, t-designs, strongly regular graphs, Ramsey colourings, codes, PΓL(2,32)
- What: assume a symmetry group, then solve a much smaller orbit system.
- Fits when: designs, strongly regular graphs, Ramsey colourings, codes.
- Lean: the object is the certificate; its symmetry also shortens the check (orbit representatives only).
- Example: all 4,996,426 simple 7-(33,8,10) designs with group PΓL(2,32); the unreduced matrix would have 4,272,048 × 13,884,156 entries ([Wassermann](https://www.mat.univie.ac.at/~slc/wpapers/s35wasser.pdf)).
- See also: T29, T46, T91

### T28 Coset decomposition
`compute` · stage: symmetry · signals: group, symmetric, exact-value
aka: God's number, Rubik's Cube, Cayley graph diameter, permutation puzzles, set cover of cosets
- What: splits the states by cosets of a subgroup and solves one representative per symmetry class.
- Fits when: diameter (God's number) problems for group actions.
- Lean: too big at Rubik scale; for small puzzles, BFS layers checked by `decide`.
- Example: the Rubik's Cube God's number is 20; symmetry and set cover cut 2,217,093,120 cosets to 55,882,296 to solve; 35 CPU-years, about 20 s per coset on a desktop ([cube20.org](https://www.cube20.org/)).
- See also: T29, T113

### T29 Computational group theory
`find` `compute` · stage: algebra · signals: group, symmetric
aka: GAP, Schreier–Sims, permutation groups, automorphism groups, character tables, group libraries, group orders
- What: group algorithms plus large data libraries.
- Fits when: finding groups with given properties, character tables, orders; computing the symmetry group to break.
- Lean: library facts are untrusted; check the specific group through its Cayley table with `decide`.
- Example: GAP 4.16.1, with thousands of functions and large data libraries ([GAP](https://www.gap-system.org/)).
- See also: T28, T30, T63

### T30 Isomorph-free generation
`compute` `prove` · stage: generate · signals: graph, set-family, classification
aka: nauty, Traces, canonical labelling, canonical augmentation, canonical construction path, orderly generation, graph enumeration, R(4,5)=25, Ramsey numbers
- What: one representative per isomorphism class via canonical labelling, orderly generation or canonical augmentation.
- Fits when: graphs, designs and codes with up to about 12–20 vertices; Ramsey-type exhaustive proofs.
- Lean: don't trust canonical forms; prove a cover lemma and check each case.
- Example: R(4,5)=25, re-proved formally in HOL4; gluing lemmas went through SAT, and a custom SAT solver with an isomorphism checker showed the cases cover everything ([Gauthier–Brown](https://arxiv.org/abs/2404.01761); [McKay–Piperno](https://arxiv.org/abs/1301.1493)).
- See also: T7, T31, T34

### T31 SAT Modulo Symmetries
`compute` `prove` · stage: generate · signals: graph, symmetric, classification
aka: SMS, lex-minimal graphs, minimality-check propagator, graphs up to isomorphism, diameter-2-critical graphs, Murty–Simon conjecture, planar graphs
- What: CDCL plus a propagator that prunes partial graphs that are not lex-minimal, so the solver generates graphs up to isomorphism.
- Fits when: enumerating or excluding graphs up to isomorphism (about 20–30 vertices).
- Lean: the pruning clauses are not RUP; they need certified symmetry steps or a Lean proof of the pruning, which is hard today.
- Example: confirmed the Murty–Simon conjecture on diameter-2-critical graphs up to 18 vertices ([Kirchweger–Szeider](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2021.34)).
- See also: T8, T24, T30
