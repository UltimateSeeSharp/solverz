# Reductions and hardness
Reductions as tools and as judges: NP-, #P-, fine-grained and parameterized hardness, PCP, and where a goal sits in the arithmetical hierarchy.

### T1000 Karp reduction and NP-completeness check
`prove` `find` `compute` · stage: judge · signals: computation
aka: NP-completeness, NP-hard, coNP-hard, polynomial-time many-one reduction, Karp's 21 problems, clique, exact cover, chromatic number, SAT, general algorithm or instance search
- What: maps a known hard problem into yours, preserving yes and no answers.
- Fits when: deciding early between hunting a general algorithm and planning instance-specific search; NP-hard means exponential search, coNP-hard means non-existence certificates may be huge.
- Lean: —
- Example: Karp (1972) reduced SAT to 21 problems, including clique, exact cover and chromatic number ([Wikipedia: Karp's 21 NP-complete problems](https://en.wikipedia.org/wiki/Karp%27s_21_NP-complete_problems)).
- See also: T1001, T1005, T1008, T154

### T1001 Reduction to a solver-friendly problem
`prove` `find` `compute` · stage: encode · signals: graph, local-constraints
aka: reduce to clique, reduce to exact cover, reduce to SAT, compatibility graph, maximum clique formulation, translation into another formalism, Keller graphs, Keller's conjecture, one engine for many problems
- What: re-expresses the question as an instance of a problem with mature exact engines (clique, exact cover, SAT).
- Fits when: the problem has a compatibility graph or covering structure; one engine and its certificate format then serve many problems.
- Lean: prove the reduction in Lean (T119); the engine returns a witness or an UNSAT certificate (T5).
- Example: Keller's conjecture in dimension 7 reduced to "no 128-clique" in three graphs, settled with symmetry breaking and SAT ([Brakensiek–Heule–Mackey–Narváez](https://arxiv.org/abs/1910.03740)).
- See also: T1, T32, T119, T1098

### T1002 LP search for optimal gadgets
`bound` · stage: relax · signals: local-constraints, inequality
aka: gadgets, gadget search, computer-found gadgets, reduction gadgets, MAX CUT hardness, MAX 3SAT, approximation ratios, LP duality, optimal local replacement
- What: restricts gadgets to a finite space, finds the best one by linear programming, and proves it optimal by LP duality.
- Fits when: a small local replacement structure with the best parameter is wanted; the dual is a rational optimality proof.
- Lean: the gadget's properties by `decide`; its optimality by the rational LP dual (T48).
- Example: computer-found gadgets gave 60/61 hardness for MAX CUT and a 0.801 algorithm for MAX 3SAT ([Trevisan–Sorkin–Sudan–Williamson](https://lucatrevisan.github.io/pubs/gadgets.pdf)).
- See also: T48, T1003

### T1003 Gap amplification and PCP hardness
`bound` · stage: judge · signals: computation, local-constraints, threshold
aka: PCP theorem, probabilistically checkable proofs, hardness of approximation, inapproximability, gap problems, constraint graphs, graph powering, expanders, Dinur
- What: amplifies the unsatisfiability gap (graph powering on expander constraint graphs) to show that approximation beyond a ratio is NP-hard.
- Fits when: judging whether an efficient method could ever beat a known ratio; shows which parameters are hard walls.
- Lean: —
- Example: Dinur's combinatorial proof of the PCP theorem ([ECCC TR05-046](https://eccc.weizmann.ac.il/report/2005/046/)).
- See also: T1004, T1002

### T1004 Unique Games and 2-to-2 conditional optimality
`bound` · stage: judge · signals: computation, graph, inequality
aka: Unique Games Conjecture, UGC, 2-to-2 games, Grassmann graph expansion, conditional hardness, Goemans–Williamson, Max-Cut 0.878, optimal SDP algorithm, stop tuning the relaxation
- What: conditional hardness that matches an algorithm's approximation ratio exactly.
- Fits when: an SDP-based algorithm looks optimal; it tells you to stop tuning the relaxation.
- Lean: —
- Example: Goemans–Williamson's 0.878 for Max-Cut is optimal under UGC ([Wikipedia: Maximum cut](https://en.wikipedia.org/wiki/Maximum_cut)); 2-to-2 games via Grassmann expansion ([Khot–Minzer–Safra](https://eccc.weizmann.ac.il/report/2018/006/)).
- See also: T1003, T1076, T1017

### T1005 Fine-grained reductions
`compute` · stage: judge · signals: computation, resource-bound
aka: SETH, strong exponential time hypothesis, 3SUM, APSP, all-pairs shortest paths, conditional lower bounds, exponent-preserving reductions, edit distance, LCS, diameter, quadratic lower bounds
- What: exponent-preserving reductions that give tight conditional time lower bounds.
- Fits when: planning a compute run; tells whether a faster exact algorithm for the inner loop is plausible.
- Lean: —
- Example: SETH-based quadratic lower bounds for edit distance, LCS and approximate diameter ([Vassilevska Williams survey](https://people.csail.mit.edu/virgi/eccentri.pdf)).
- See also: T1006, T1122

### T1006 ETH and sparsification
`compute` · stage: judge · signals: computation, resource-bound
aka: exponential time hypothesis, sparsification lemma, k-SAT, 3-SAT 2^{Ω(n)}, no 2^{o(n)} colouring, k-clique n^{o(k)}, treewidth lower bounds, independent set on treewidth-w graphs, how large n exhaustive search can reach
- What: assumes 3-SAT needs 2^{Ω(n)} time; sparsification transfers this to k-SAT and many graph problems.
- Fits when: estimating the largest n an exhaustive search can reach; it rules out 2^{o(n)} colouring and n^{o(k)} k-clique. Unresolved: Wikipedia (opened 2026-11-04) reports claimed disproofs that are not peer-reviewed; check their status before relying on ETH.
- Lean: —
- Example: SETH gives tight (2−o(1))^w bounds for independent set on graphs of treewidth w ([Wikipedia: Exponential time hypothesis](https://en.wikipedia.org/wiki/Exponential_time_hypothesis)).
- See also: T1005, T1007, T154

### T1007 Parameterized hardness (W[1])
`compute` `find` · stage: judge · signals: computation, resource-bound
aka: W-hierarchy, W[1]-hard, W[1]-complete, fpt-reduction, fixed-parameter tractable, FPT, f(k)·n^{O(1)}, clique, independent set, which parameter to exploit
- What: fpt-reductions show that no f(k)·n^{O(1)} algorithm is likely.
- Fits when: choosing which parameter (solution size, treewidth, symmetry) to exploit.
- Lean: —
- Example: Clique and Independent Set are W[1]-complete ([Wikipedia: Parameterized complexity](https://en.wikipedia.org/wiki/Parameterized_complexity)).
- See also: T1124, T1126, T1127

### T1008 #P-hardness of counting
`compute` · stage: judge · signals: computation, exact-value
aka: #P-complete, counting complexity, permanent, 0/1 permanent, counting perfect matchings, counting harder than deciding, planarity, bounded width
- What: counting can be hard even when deciding is easy.
- Fits when: compute problems that ask for exact counts; a hint to look for planarity, bounded width or symmetry instead.
- Lean: —
- Example: the 0/1 permanent is #P-complete ([Wikipedia: Permanent](https://en.wikipedia.org/wiki/Permanent_(mathematics))).
- See also: T38, T1128, T1119, T1123

### T1009 Self-reducibility
`find` · stage: search · signals: computation, construction
aka: search to decision, search from counting, fix coordinates one by one, oracle queries, recover the object, set partitions from counts
- What: fixes the coordinates of a solution one at a time, querying a decision or counting oracle after each.
- Fits when: a fast feasibility test or count exists but the object itself is needed.
- Lean: the recovered object by `decide`.
- Example: set-partition algorithms recover partitions from inclusion–exclusion counts by self-reducibility ([Björklund–Husfeldt–Koivisto](https://www.cs.helsinki.fi/u/mkhkoivi/publications/sicomp-2009.pdf)).
- See also: T1113

### T1010 Arithmetical-hierarchy classification of the goal
`prove` `find` · stage: judge · signals: logic, computation
aka: Σ1, Π1, Π2, Σ⁰₁, Π⁰₁, r.e., co-r.e., finite witness, finite counterexample, conjecture as a halting problem, small Turing machine never halts, Busy Beaver, independence risk, size of a conjecture
- What: Σ1 claims have finite witnesses, Π1 claims have finite counterexamples, Π2 and above have neither; a Π1 conjecture can be written as "this small Turing machine never halts".
- Fits when: before taking on a problem: decides whether a finite Lean check can exist and which kind (find = Σ1, refute = Π1) it is; the size of a machine that encodes the conjecture links it to Busy Beaver values and to independence risk.
- Lean: Mathlib has partial recursive functions and the undecidability of halting (`ComputablePred`, `halting_problem` in `Mathlib/Computability/Halting.lean`).
- Example: Σ⁰₁ = r.e., Π⁰₁ = co-r.e., totality of Turing machines is Π⁰₂ ([Wikipedia: Arithmetical hierarchy](https://en.wikipedia.org/wiki/Arithmetical_hierarchy)); Busy Beaver values versus set theory and number theory ([Aaronson, The Busy Beaver Frontier](https://www.scottaaronson.com/papers/bb.pdf)).
- See also: T37, T154, T1085
