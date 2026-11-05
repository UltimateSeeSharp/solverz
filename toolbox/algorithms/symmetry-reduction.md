# Symmetry reduction in search
Symmetry tools beyond static breaking and prescribed groups (T24–T29): dynamic breaking, orbitopes, move-order reduction, abstraction.

### T1094 Symmetry breaking during search (SBDS)
`find` `compute` · stage: symmetry · signals: symmetric, colouring
aka: SBDS, dynamic symmetry breaking, symmetric nogoods, constraint programming, Gent–Smith, n-queens, autocorrelation sequences, graph colouring symmetries, Ramsey symmetries
- What: after backtracking from a choice, posts its symmetric images as forbidden.
- Fits when: CP search with heuristics you do not want to constrain.
- Lean: as for T24: the pruning needs a Lean soundness proof or a certified redundancy proof (T25).
- Example: n-queens and autocorrelation sequences; graph colouring and Ramsey symmetries ([Gent–Smith](https://research-portal.st-andrews.ac.uk/en/publications/symmetry-breaking-in-constraint-programming/)).
- See also: T24, T25

### T1095 Orbitopal fixing
`find` `bound` · stage: symmetry · signals: symmetric, colouring
aka: orbitopes, partitioning symmetry, interchangeable colour classes, arbitrary class labels, variable fixing, graph partitioning, Kaibel–Peinhardt–Pfetsch, ILP symmetry
- What: linear-time variable fixing for partitioning symmetry (interchangeable colour classes).
- Fits when: colouring or partition formulations where class labels are arbitrary.
- Lean: as for T24.
- Example: graph partitioning ([Kaibel–Peinhardt–Pfetsch](https://arxiv.org/abs/math/0611531)).
- See also: T24, T26

### T1096 Partial-order reduction
`compute` `prove` · stage: symmetry
aka: canonical move order, commuting moves, independent steps, stubborn sets, persistent sets, sleep sets, model checking, adding edges, placing pieces
- What: explores only one order of commuting moves.
- Fits when: the same object is reached by permuting independent steps (adding edges, placing pieces).
- Lean: — (part of the search; the result needs the search's own certificate)
- Example: stubborn, persistent and sleep sets ([Wikipedia: Partial order reduction](https://en.wikipedia.org/wiki/Partial_order_reduction)).
- See also: T16, T1133

### T1097 Abstraction then concretization
`compute` `prove` · stage: symmetry · signals: colouring, graph, symmetric
aka: degree matrices, abstract colourings, lift abstract solutions, multicolour Ramsey numbers, R(4,3,3)=30, edge colourings, Codish
- What: solves an abstract version (e.g. degree matrices) up to symmetry, then lifts each abstract solution.
- Fits when: multicolour Ramsey and edge-colouring problems.
- Lean: prove that every concrete object maps to a listed abstraction, then certify each lift as a SAT case (T5).
- Example: R(4,3,3)=30 via abstraction and symmetry breaking ([Codish–Frank–Itzhakov–Miller](https://arxiv.org/abs/1510.08266)).
- See also: T24, T30
