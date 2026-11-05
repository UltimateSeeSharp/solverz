# Engineering and design methods
Methods from engineering, software and design practice: trade-offs, systematic variation, bottlenecks, adversarial checks and backward planning.

### T1311 TRIZ contradictions
`prove` `bound` · stage: practice
aka: TRIZ, Altshuller, technical contradiction, trade-off, separation principles, separate by scale, case or iteration, efficiency vs flexibility, density vs structure, GPY barrier, Zhang
- What: names the two parameters where improving one worsens the other and resolves the conflict with known principles instead of a compromise.
- Fits when: a proof has a trade-off (two error terms, efficiency vs flexibility, density vs structure); write it explicitly and separate the two by scale, case or iteration step.
- Lean: —
- Example: Altshuller's patent study ([Wikipedia: TRIZ](https://en.wikipedia.org/wiki/TRIZ)); Zhang took a less efficient but more flexible sieve and broke the GPY barrier ([Quanta](https://www.quantamagazine.org/yitang-zhang-proves-landmark-theorem-in-distribution-of-prime-numbers-20130519/)).
- See also: T1312, T1368

### T1312 Ideal final result
`bound` `prove` · stage: reformulate
aka: TRIZ ideal final result, IFR, perfect certificate, magic function, auxiliary function, tight at every needed point, sphere packing, Viazovska
- What: describes the outcome where "the desired result is achieved by itself", then works toward it.
- Fits when: a bound needs a certificate; describe the perfect one (a function tight at every needed point, a polynomial vanishing exactly where wanted) and ask what family could produce it.
- Lean: —
- Example: the sphere-packing bound needed a function vanishing with its Fourier transform at the lattice points; Viazovska built it from modular forms ([Wikipedia: Sphere packing](https://en.wikipedia.org/wiki/Sphere_packing)).
- See also: T50, T1311, T1373

### T1313 Morphological analysis
`find` `prove` `bound` `compute` · stage: practice
aka: Zwicky box, morphological box, parameter table, combinations, setting × object × tool × quantity, empty cells, Kelley–Meka
- What: lists independent parameters and their options in a box, enumerates combinations and removes inconsistent ones.
- Fits when: looking for an untried attack; tabulate setting × object × tool × quantity (integers, F_p^n, graphs; density increment, polynomial, entropy, spectral) and try the empty cells.
- Lean: —
- Example: [Wikipedia: Morphological analysis (problem-solving)](https://en.wikipedia.org/wiki/Morphological_analysis_(problem-solving)); Kelley–Meka built their tools in the finite-field cell, then moved to the integers ([arXiv:2302.05537](https://arxiv.org/abs/2302.05537)).
- See also: T1362, T1363

### T1314 Design of experiments
`find` `bound` `compute` · stage: explore
aka: DOE, factorial design, randomisation, blocking, replication, sequential design, parameter sweep, seeds, Fisher, millions of simulations, Kadison–Singer
- What: varies several factors at once with randomisation, blocking and replication; sequential designs pick the next run from results.
- Fits when: runs over parameter grids (n, field, construction family, seed); sweep them jointly, not one factor at a time, and replicate random searches before trusting a trend.
- Lean: —
- Example: Fisher's principles ([Wikipedia: Design of experiments](https://en.wikipedia.org/wiki/Design_of_experiments)); Marcus–Spielman–Srivastava ran millions of simulations, found no counterexample, and bet on "true" ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)).
- See also: T100, T1310, T1334

### T1315 Theory of constraints
`bound` · stage: practice
aka: TOC, bottleneck, binding constraint, identify exploit elevate, limiting lemma, limiting parameter, GPY, level of distribution
- What: output is limited by one constraint; identify, exploit and elevate it, then find the next.
- Fits when: a bound is stuck; find the single lemma or parameter that limits it and put all effort there.
- Lean: —
- Example: [Wikipedia: Theory of constraints](https://en.wikipedia.org/wiki/Theory_of_constraints); GPY needed a level of distribution above 1/2 and nothing else ([Quanta](https://www.quantamagazine.org/yitang-zhang-proves-landmark-theorem-in-distribution-of-prime-numbers-20130519/)).
- See also: T1311

### T1316 Bisection
`compute` · stage: explore · signals: threshold
aka: binary search, git bisect, where a property switches, threshold location, critical n, critical dimension, Keller's conjecture
- What: binary search over versions or parameters for where behaviour changes.
- Fits when: a property holds for small n, dimension or k and fails later; the switch point is often the theorem.
- Lean: —
- Example: git bisect ([Wikipedia: Delta debugging](https://en.wikipedia.org/wiki/Delta_debugging)); Keller holds up to dimension 7, fails from 8 ([Wikipedia: Keller's conjecture](https://en.wikipedia.org/wiki/Keller%27s_conjecture)).
- See also: T123

### T1317 Rubber-duck explanation
`prove` · stage: practice
aka: rubber duck debugging, explain line by line, reader with no context, refereeing, finding the gap, Wiles's gap, Katz
- What: explaining line by line to an inert listener exposes the gap between intent and reality.
- Fits when: a proof looks finished; write every step for a reader with no context.
- Lean: formalisation is the strict form.
- Example: [Wikipedia: Rubber duck debugging](https://en.wikipedia.org/wiki/Rubber_duck_debugging); Katz found Wiles's gap while refereeing it ([Wikipedia: Wiles's proof of Fermat's Last Theorem](https://en.wikipedia.org/wiki/Wiles%27s_proof_of_Fermat%27s_Last_Theorem)).
- See also: T1318

### T1318 Red teaming
`find` `prove` `bound` `compute` · stage: practice
aka: red team, adversary, refuter, independent recomputation, attack every result, Ellingsrud–Strømme, mirror symmetry
- What: a team plays the adversary to find weaknesses first.
- Fits when: before a result counts: an independent refuter attacks it, and an independent recomputation catches bugs on either side.
- Lean: —
- Example: [Wikipedia: Red team](https://en.wikipedia.org/wiki/Red_team); Ellingsrud–Strømme's rigorous count disagreed with the physicists' until they found a bug in their own code ([Wikipedia: Mirror symmetry (string theory)](https://en.wikipedia.org/wiki/Mirror_symmetry_(string_theory))).
- See also: T83, T1317, T1356

### T1319 Pre-mortem
`prove` · stage: practice
aka: premortem, assume failure, prospective hindsight, failure modes, broken step, counterexample family
- What: assumes the project already failed and asks what went wrong.
- Fits when: a planned proof is about to take serious effort; assume it turned out false, name the broken step and the counterexample family, and test those first.
- Lean: —
- Example: [Wikipedia: Pre-mortem](https://en.wikipedia.org/wiki/Pre-mortem).
- See also: T1334, T1370

### T1320 Feasibility studies
`prove` · stage: practice
aka: cheap trial, top-down sketch, low-resolution outline, kill weak lines early, Polymath rules, short non-technical comments
- What: short, cheap trials before committing.
- Fits when: a new attack line; sketch the whole argument top-down at low resolution and kill weak lines early.
- Lean: —
- Example: a Polymath rule: begin with "short, non-technical comments" as feasibility studies ([Gowers](https://gowers.wordpress.com/2009/01/27/is-massively-collaborative-mathematics-possible/)).
- See also: T1319, T1354

### T1321 Retrosynthesis
`prove` · stage: reformulate
aka: retrosynthetic analysis, Corey, disconnection, precursors, synthesis tree, backward chaining, lemma tree, goal tree
- What: disconnects a target molecule into simpler precursors until reaching available ones; a search tree of disconnections.
- Fits when: a goal has several possible last steps; list the lemmas that would give it in one step, recursively, until hitting known theorems, and keep the tree.
- Lean: —
- Example: Corey's retrosynthetic analysis ([Wikipedia: Retrosynthetic analysis](https://en.wikipedia.org/wiki/Retrosynthetic_analysis)).
- See also: T150
