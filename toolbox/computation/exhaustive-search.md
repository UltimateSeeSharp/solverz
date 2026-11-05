# Exhaustive search and case analysis
Complete enumeration with pruning, case splits and checkable partial results, outside plain SAT.

### T32 Exact cover with Dancing Links
`find` `prove` `compute` · stage: search · signals: geometry, set-family, construction
aka: Algorithm X, DLX, exact cover, reversible linked-list updates, polyomino tilings, Latin squares, designs, puzzles
- What: backtracking with reversible linked-list updates.
- Fits when: tilings, Latin squares, designs, puzzles.
- Lean: a cover by `decide`; non-existence needs a search tree or a SAT proof.
- Example: Knuth's polyomino tiling searches ([Dancing Links](https://arxiv.org/abs/cs/0011047)).
- See also: T1, T33

### T33 Hitting-set enumeration
`compute` `prove` · stage: search · signals: set-family, exact-value
aka: unavoidable sets, minimum number of clues, critical sets, Sudoku, 17-clue Sudoku, transversals
- What: enumerates sets that hit every member of a family of unavoidable sets.
- Fits when: minimum-clue and critical-set problems.
- Lean: the search is too large; formalize the reduction and check small analogues.
- Example: there is no 16-clue Sudoku; the minimum is 17 ([McGuire–Tugemann–Civario](https://arxiv.org/abs/1201.0749)).
- See also: T32

### T34 Gluing small objects with LP case pruning
`bound` `prove` · stage: search · signals: graph, colouring, inequality
aka: gluing, catalogues of small graphs, neighbourhood decomposition, Ramsey upper bounds, R(5,5) ≤ 46, extremal numbers
- What: builds large objects from enumerated parts; LP bounds remove most cases.
- Fits when: Ramsey upper bounds and extremal numbers.
- Lean: LP steps as rational dual certificates (`linarith`, T48), cases by `decide` or SAT; heavy.
- Example: R(5,5) ≤ 46, by linear programming plus a large case check, implemented independently by both authors ([Angeltveit–McKay](https://arxiv.org/abs/2409.15709)).
- See also: T30, T48

### T35 Branch-and-bound over combinatorial types
`prove` `bound` · stage: search · signals: geometry, inequality
aka: contact graphs, tame graphs, Tammes problem, spherical codes, sphere packing, Kepler conjecture, Flyspeck
- What: enumerates contact graphs or tame graphs and excludes each by LP or interval numerics.
- Fits when: optimality of packings and spherical codes for small N.
- Lean: LP duals and interval checks for each case; Flyspeck's scale is out of reach, small N may be within reach.
- Example: the Tammes problem for N=14 ([Musin–Tarasov](https://arxiv.org/abs/1410.2536)); the Kepler conjecture, checked in HOL Light and Isabelle ([Flyspeck](https://arxiv.org/abs/1501.02155)).
- See also: T48, T64

### T36 Symmetry-reduced generate-and-prune plus SAT
`prove` `bound` · stage: search · signals: order, symmetric, impossibility
aka: sorting networks, comparator networks, optimal size, 0-1 principle, Floyd's network, generate-and-prune, small circuits
- What: prunes by symmetry, then hands the rest to SAT.
- Fits when: optimal sizes of small networks and circuits.
- Lean: one network by the 0-1 principle, with `decide` over 2^n inputs packed as bitsets (T121); the 0-1 principle is not in Mathlib; optimality needs the exhaustive proof.
- Example: 9-input sorting networks need 25 comparators, so Floyd's network is optimal ([Codish et al.](https://arxiv.org/abs/1405.5754)).
- See also: T1, T24

### T37 Decider portfolios over enumerated programs
`compute` `prove` · stage: search · signals: computation, classification
aka: busy beaver, BB(5), Turing machines, halting problem, bbchallenge, loop detection, n-gram closed position sets, finite-automata reduction
- What: enumerates all machines, applies cheap deciders (loops, n-gram closed position sets, finite-automata reduction), and hand-proves the sporadic rest.
- Fits when: classifying a finite set of programs by halting.
- Lean: Coq-BB5 used `native_compute`, which does not count; a kernel-only port needs structurally recursive deciders.
- Example: BB(5): S(5)=47,176,870 over 181,385,789 machines, proved in Coq ([bbchallenge](https://arxiv.org/abs/2509.12337)).
- See also: T16, T120

### T38 Orbit-based exact counting with checkable partial results
`compute` · stage: search · signals: set-family, symmetric, exact-value
aka: Dedekind numbers, D(9), monotone Boolean functions, counting over orbits, matrix and DP formulations, partial sums, FPGA counting
- What: matrix and DP formulations over orbits, split into partial results that can be checked separately.
- Fits when: exact counts (compute).
- Lean: not at D(9) scale; publishing independently checkable partial results is the pattern to copy.
- Example: the 9th Dedekind number D(9), computed on FPGAs; it came with 490 million partial results, each checkable on a CPU ([Van Hirtum et al.](https://arxiv.org/abs/2304.03039); [Jäkel](https://arxiv.org/abs/2304.00895)).
- See also: T12, T122, T152

### T39 Algebraic sequence search for matrices
`find` · stage: search · signals: matrix, sequence, construction
aka: Hadamard matrices, Hadamard conjecture, weighing matrices, difference sets, Turyn-type sequences, base sequences, T-sequences, autocorrelation, ±1 sequences, order 428
- What: finds short ±1 sequences with vanishing combined autocorrelation, then builds matrices from arrays.
- Fits when: Hadamard matrices, weighing matrices, difference sets.
- Lean: the sequence autocorrelations by `decide` (O(n²) small integers); prove the array construction once.
- Example: a Hadamard matrix of order 428, from Turyn-type sequences of lengths 36, 36, 36, 35 turned into base sequences and then T-sequences ([Kharaghani–Tayfeh-Rezaie](https://www.cs.uleth.ca/~hadi/research/h428.pdf)).
- See also: T27, T94
