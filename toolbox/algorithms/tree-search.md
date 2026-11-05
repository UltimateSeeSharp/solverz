# Tree and state-space search
Branch and bound, heuristic and frontier search, run-size estimation, restarts, parallel load balancing, and Ramsey and design case splits.

### T1098 Branch and bound with colouring bounds
`find` `bound` `compute` · stage: search · signals: graph, exact-value
aka: Cliquer, Östergård's algorithm, maximum clique, maximum independent set, clique number, greedy colouring bound, Ramsey and coding subproblems
- What: bounds the clique size by a greedy colouring of the candidates.
- Fits when: maximum clique or independent set inside Ramsey and coding problems.
- Lean: a clique by `decide`; "no larger clique" needs the search tree or a SAT proof (T5).
- Example: Cliquer, Östergård's exact algorithm ([Cliquer](https://users.aalto.fi/~pat/cliquer.html)).
- See also: T1001, T1

### T1099 Branch and cut
`bound` `compute` · stage: search · signals: graph, inequality
aka: cutting planes, LP bounds at every node, Concorde, travelling salesman, TSPLIB, polyhedral knowledge, ILP
- What: strengthens the LP bound with cutting planes at every node of a branch-and-bound tree.
- Fits when: ILP-shaped optimization with good polyhedral knowledge.
- Lean: a tree certificate with exact cuts (T49).
- Example: Concorde solved all TSPLIB instances up to 85,900 cities ([Concorde](https://www.math.uwaterloo.ca/tsp/concorde.html)).
- See also: T49, T1078

### T1100 IDA* with pattern databases
`compute` · stage: search · signals: group, exact-value
aka: iterative deepening A*, admissible heuristics, pattern databases, abstracted subproblems, shortest solutions, optimal solutions, Rubik's Cube, Korf
- What: iterative deepening guided by admissible heuristics taken from exact distances in abstracted subproblems.
- Fits when: shortest-solution searches in huge state spaces; memory trades for time.
- Lean: a solution sequence by `decide`; optimality needs the search as a certificate.
- Example: the first optimal solutions of random Rubik's Cubes ([Korf](https://www.cs.princeton.edu/courses/archive/fall06/cos402/papers/korfrubik.pdf)).
- See also: T28, T1101

### T1101 Frontier search and delayed duplicate detection
`compute` · stage: search · signals: exact-value
aka: breadth-first search beyond RAM, disk-based BFS, DDD, hash-partitioned files, sorting-based duplicate detection, 15-puzzle, four-peg Towers of Hanoi, Korf–Schultze
- What: keeps only the search frontier and detects duplicates later, by sorting or by hashing states into files processed in parallel.
- Fits when: exhaustive BFS of state spaces larger than RAM; F: is write-bound, so prefer hash-based DDD.
- Lean: — (too large; small state spaces by BFS layers and `decide`, as in T28)
- Example: the first complete BFS of the 15-puzzle, 10¹³ states ([Korf–Schultze](https://ai.dmi.unibas.ch/_files/teaching/fs21/ai/material/ai10-korf-schultze-aaai2005.pdf)); four-peg Towers of Hanoi to 22 discs ([Korf](https://www.cp.eng.chula.ac.th/~prabhas/teaching/ioi2007/olympic2007/korf.txt)).
- See also: T1136, T1137, T154

### T1102 Random-probe size estimation
`find` `prove` `compute` · stage: judge
aka: Knuth's estimator, backtrack tree size, 1 + b₁ + b₁b₂ + …, random root-to-leaf probes, random canonical construction paths, estimating class size, feasibility on one PC, days or centuries, comparing encodings
- What: estimates a search tree's size from random root-to-leaf probes (1 + b₁ + b₁b₂ + …); along random canonical construction paths it estimates class sizes without full generation.
- Fits when: before any long run: predicts days versus centuries, compares encodings, and decides whether a full enumeration fits one PC.
- Lean: —
- Example: [Knuth 1975, Estimating the efficiency of backtrack programs](https://rupak.pages.mpi-sws.org/sv2025/assets/pdfs/Knuth1975.pdf); approximate counting via canonical augmentation ([McKay 1998](https://users.cecs.anu.edu.au/~bdm/papers/orderly.pdf)).
- See also: T154, T30, T1323

### T1103 Randomized restarts
`find` `compute` · stage: search
aka: restart schedules, heavy-tailed run times, run-time distributions, seeds, probSAT, CDCL restarts
- What: restarts a randomized search on a schedule; heavy-tailed run times make restarts faster in expectation.
- Fits when: run times vary by orders of magnitude between seeds.
- Lean: — (only the final witness or certificate counts)
- Example: optimal restart times for probSAT estimated from run-time distributions ([arXiv:1904.11757](https://arxiv.org/abs/1904.11757)); restarts in CDCL ([Wikipedia: Conflict-driven clause learning](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)).
- See also: T1, T2

### T1104 Work stealing
`compute` · stage: search
aka: Cilk scheduler, load balancing, irregular backtracking trees, parallel depth-first search, idle threads steal subtrees, T₁/P + O(T∞)
- What: idle threads steal subtrees from busy ones.
- Fits when: irregular backtracking trees on the 14 usable threads here.
- Lean: —
- Example: the Cilk scheduler, T₁/P + O(T∞) ([Wikipedia: Work stealing](https://en.wikipedia.org/wiki/Work_stealing)).
- See also: T1136, T153

### T1105 Minimum-edge bounds e(s,t,n)
`bound` `prove` · stage: search · signals: graph, colouring, inequality
aka: minimum number of edges, (s,t,n)-graphs, Ramsey graphs, forced degrees, forced regularity, critical graphs, R(3,10) ≤ 42, Goedgebeur–Radziszowski
- What: computes exact minimum edge counts of small Ramsey graphs to force the degrees, or the regularity, of a critical graph.
- Fits when: Ramsey upper bounds; turns a global question into a search over regular graphs.
- Lean: each edge-count lemma needs its own certificate; the final regular-graph search as SAT cases (T5).
- Example: R(3,10) ≤ 42 by forcing 9-regularity and excluding it ([Goedgebeur–Radziszowski](https://arxiv.org/abs/1210.5826)).
- See also: T34, T30

### T1106 Forced local structure plus orbit case split
`bound` `prove` · stage: search · signals: set-family, symmetric, impossibility
aka: double counting, forced links, forced degrees, orbit case split, covering designs, covering numbers, C(12,6,4)=41, certified SAT cases, cake_lpr, Krug
- What: double counting forces degrees and links; the rest splits by the orbits of a group, and each case is certified.
- Fits when: covering and design bounds with a certificate per case.
- Lean: the counting lemmas by hand; each case as an LRAT certificate (T5, T122).
- Example: C(12,6,4)=41 via forced links and the orbits of a group of order 3840, with SAT cases checked by cake_lpr ([Krug 2026](https://arxiv.org/abs/2607.23766)).
- See also: T6, T26, T122
