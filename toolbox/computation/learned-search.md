# Learned generative search
Neural networks and reinforcement learning that propose objects or move sequences; the output is checked exactly.

### T101 Deep cross-entropy method
`find` · stage: local-search · signals: graph, matrix, construction
aka: cross-entropy method, reinforcement learning for counterexamples, graph counterexamples, spectral graph conjectures, eigenvalue conjectures, Brualdi–Cao
- What: a net generates objects, is retrained on the top percentile, and repeats.
- Fits when: graph or matrix counterexamples to inequalities.
- Lean: the counterexample by `decide`, or by exact eigenvalue bounds (characteristic polynomial sign changes).
- Example: refuted a Brualdi–Cao question and several eigenvalue conjectures ([Wagner](https://arxiv.org/abs/2104.14516)).
- See also: T90, T102

### T102 PatternBoost
`find` · stage: local-search · signals: graph, construction
aka: transformer plus local search, learned constructions, extremal combinatorics, learnable structure
- What: alternates local search with a transformer trained on the best constructions.
- Fits when: extremal combinatorics where good objects share learnable structure.
- Lean: object check by `decide`.
- Example: a counterexample to a 30-year-old conjecture, and best-known solutions to several problems ([Charton–Ellenberg–Wagner–Williamson](https://arxiv.org/abs/2411.00566)).
- See also: T95, T101

### T103 Transformers trained on synthetic solved instances
`find` · stage: local-search · signals: dynamics, polynomial, construction
aka: backward generation, seq2seq oracle, Lyapunov functions, symbolic integration, easy to verify but hard to find
- What: generates problem/solution pairs backwards, trains a seq2seq model, and uses it as an oracle.
- Fits when: objects that are easy to verify but hard to find (Lyapunov functions, integrals).
- Lean: a candidate Lyapunov function becomes a polynomial inequality, checked by SOS (T54) or `nlinarith`.
- Example: new Lyapunov functions for non-polynomial systems ([Alfarano–Charton–Hayat](https://arxiv.org/abs/2410.08304)).
- See also: T54, T58

### T104 AlphaZero-style decomposition game
`find` `bound` · stage: local-search · signals: matrix, product-structure, construction
aka: AlphaTensor, tensor decomposition as a game, matrix multiplication algorithms, tensor rank, Strassen, single-player game, finite fields
- What: turns tensor decomposition into a single-player game over a discrete coefficient set; reaching zero is proof of correctness.
- Fits when: algebraic complexity (rank) upper bounds.
- Lean: the decomposition is an exact identity, checked by `ring`/`decide`.
- Example: AlphaTensor beat Strassen's two-level algorithm for 4×4 matrices over a finite field ([Fawzi et al.](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC9534758/fullTextXML)).
- See also: T92, T108

### T105 RL for move sequences on group presentations
`find` · stage: local-search · signals: group, construction
aka: Andrews–Curtis conjecture, AC moves, balanced presentations, Akbulut–Kirby presentations, Miller–Schupp presentations, trivializations, path finding
- What: an agent searches for long Andrews–Curtis move paths.
- Fits when: finding (or failing to find) trivializations; path-finding certificates.
- Lean: the move sequence is a certificate, replayed on words by `decide`.
- Example: all but two Akbulut–Kirby presentations shown length-reducible, plus three Miller–Schupp subfamilies resolved ([Shehper et al.](https://arxiv.org/abs/2408.15332)).
- See also: T63

### T106 RL for knot diagram moves
`bound` · stage: local-search · signals: topology, inequality
aka: unknotting number, crossing changes, knot diagrams, upper bounds on knot invariants, reinforcement learning
- What: an agent finds short sequences of crossing changes that unknot a diagram.
- Fits when: upper bounds on knot invariants.
- Lean: diagram moves are combinatorial and replayable, but knot theory is barely in Mathlib.
- Example: unknotting numbers of 57k knots, and 43 previously unknown values (assuming additivity) ([Applebaum et al.](https://arxiv.org/abs/2409.09032)).
- See also: T86
