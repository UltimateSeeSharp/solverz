# Toolbox

Techniques mathematicians and scientists use on hard problems: what each
does, when it fits, an example. A starting point, never a boundary: an idea
from outside it counts the same as one from inside.

## Lookup
1. Tag the problem with its Object and Goal signals, and Structure or
   Situation ones where they hold.
2. Rank entries by shared Object signals, then by the others; read from the
   top. Kind is a hint, not a filter.
3. `router.md`: the stages of an attack of this kind and their families.
4. Grep `aka:` and `Fits when` for the problem's objects and situation in
   your own words.
5. Stuck: `stuck.md`, keyed by situation.

## Entry
```
### T412 Combinatorial Nullstellensatz
`prove` `find` · stage: argue · signals: polynomial, additive
aka: Alon's Nullstellensatz
- What: a nonzero coefficient of a suitable polynomial forces a good point in a grid.
- Fits when: the property becomes "some product of linear forms is nonzero".
- Lean: one coefficient by `decide`.
- Example: Cauchy–Davenport, list colouring ([Alon 1999](https://…)).
- See also: T398, T415
```
IDs `T` (techniques) and `S` (case studies), stable, never reused. Lean
says how a result of the technique gets checked, or `—`. Signals: 0–4,
none when none fits; a method is found by its stage.

A case study, in `breakthroughs/`, grouped by what unlocked it:
```
### S7 Sensitivity conjecture
Stuck: 1992–2019 · `prove` · used: T233, T241
- Unlock: a signed adjacency matrix of the cube and Cauchy interlacing (Huang).
- From: spectral graph theory.
- Source: [Huang 2019](https://…)
```

## Stages
One per entry: what the technique does in an attack.
- `argue`: a proof technique.
- `construct`: builds an object explicitly.
- `explore`: finds what is probably true: experiments with data, numerics, heuristic predictions.
- `reformulate`: restates the problem in another form: a duality, another field's language, a special or general case.
- `encode`: restates a problem as solver input (SAT, ILP, CP, clique).
- `symmetry`: shrinks a space by its symmetries.
- `search`: exhaustive or complete search.
- `local-search`: heuristic search over objects.
- `program-search`: searches over programs that build objects.
- `generate`: lists objects up to isomorphism.
- `relax`: LP, SDP and other relaxations with dual certificates.
- `game-search`: solves games by search.
- `algebra`: exact symbolic computation (computer algebra, lattice reduction, factoring).
- `enclose`: rigorous numerics (interval and enclosure methods).
- `decide`: automated provers and decision procedures outside Lean.
- `certify`: makes a result checkable (certificate design, checkers).
- `lean-tooling`: Lean tactics, libraries and checking practice.
- `judge`: decides whether an approach can work (barriers, size estimates).
- `practice`: research practice and ways out of a deadlock.

A solver is `search`; turning a problem into its input is `encode`; restating
it as mathematics is `reformulate`. Learned or RL search over objects is
`local-search`; `game-search` is for solving two-player games.

## Signals

**Object**
- `graph`: graphs and hypergraphs, subgraphs, independence, spectra.
- `set-family`: families of subsets, Boolean functions, the cube, designs, codes.
- `colouring`: colourings that must avoid or force a pattern (Ramsey, van der Waerden, chromatic).
- `integers`: divisibility, primes, Diophantine equations, arithmetic functions.
- `arithmetic-geometry`: curves, rational points, modular forms, Galois representations, L-functions.
- `finite-field`: F_q and F_qⁿ models, character and exponential sums, finite geometry.
- `additive`: sumsets, progressions, sum-free and zero-sum sets.
- `polynomial`: polynomials, varieties, properties written as polynomial conditions.
- `matrix`: matrices, linear maps, eigenvalues, rank, tensors.
- `group`: groups, rings, fields, representations.
- `sequence`: sequences, recurrences, words, generating functions.
- `order`: permutations, posets, lattices.
- `game`: two-player or positional games and their strategies.
- `geometry`: discrete and convex geometry: points, lines, packings, tilings, polytopes.
- `topology`: spaces, maps, fixed points, embeddings.
- `analytic`: real or complex functions, integrals, inequalities over R.
- `pde`: PDE, variational problems, geometric analysis.
- `dynamics`: iterated maps, orbits, flows.
- `random`: random structures, probabilities.
- `computation`: complexity classes, machines, decidability.
- `logic`: definability, independence, infinite sets.
- `operator`: Banach and Hilbert spaces, operators.
- `manifold`: differential, Riemannian and symplectic geometry.
- `quantum`: quantum states, channels, nonlocal games.

**Goal**
- `construction`: an explicit object: a witness, a record, a counterexample.
- `impossibility`: no object exists; an obstruction is wanted.
- `exact-value`: an exact number, count or generating function.
- `asymptotic`: a growth rate, constant or exponent as n → ∞.
- `identity`: two expressions are equal.
- `inequality`: one quantity bounds another.
- `congruence`: divisibility or a congruence.
- `classification`: all objects of a type, up to isomorphism.
- `threshold`: where a property switches on (density, probability, parameter).
- `resource-bound`: how many queries, bits, gates or steps a task needs.

**Structure**
- `symmetric`: a large group acts on the problem or its extremal objects.
- `regular-structure`: periodic, automatic, recursive or self-similar patterns.
- `pseudorandom`: extremal objects look spread out or random.
- `dense`: positive density; counting and regularity apply.
- `sparse`: few elements or edges; local and sparse-analogue arguments.
- `local-constraints`: many constraints, each on few variables.
- `parity`: an involution, pairing or parity count is in view.
- `product-structure`: objects combine by products, tensor powers or concatenation.

**Situation**
- `near-miss`: the best objects found almost have the property.
- `induction-stuck`: the step from n to n + 1 does not close.
- `barrier`: known methods provably cannot reach the target.
- `numeric-only`: only floating-point evidence; an exact or rigorous version is needed.

## Families

**Pure math**
- [Proof strategies](pure-math/proof-strategies.md): General moves for an open problem: specialize, generalize, reformulate, strengthen, embed, dualize, compactify, and reduce to a finite check.
- [Elementary combinatorial principles](pure-math/elementary-combinatorics.md): Pigeonhole, averaging, double counting, extremal choices, invariants and monovariants, parity, descent, induction, bijections, involutions, inclusion–exclusion, LYM, chain decompositions and compression.
- [Extremal combinatorics](pure-math/extremal-combinatorics.md): Turán-type and density problems: symmetrization, stability, regularity and removal, containers, absorption, nibble and random greedy, spread measures, entropy, graph limits, algebraic constructions, correlation inequalities.
- [Probabilistic method](pure-math/probabilistic-method.md): Random constructions and their estimates in combinatorics: first and second moments, alteration, local lemmas, Janson, concentration, Poisson approximation, tailored distributions, random-algebraic hybrids, random regular graphs.
- [Algebraic and spectral methods in combinatorics](pure-math/algebraic-combinatorics.md): Polynomials, linear algebra and eigenvalues as proof tools: Nullstellensatz, Chevalley–Warning, polynomial method, slice rank, partitioning, dimension arguments, interlacing, real-stable and Lorentzian polynomials, determinants.
- [Additive combinatorics](pure-math/additive-combinatorics.md): Patterns in dense and sparse sets of integers and groups: density and energy increments, Gowers norms, transference, sumset calculus, Freiman and Bogolyubov, almost periodicity, sifting, entropic sumsets, sum-product, Behrend, growth in groups.
- [Ramsey theory](pure-math/ramsey-theory.md): Monochromatic structure in colourings: iterated pigeonhole, the book algorithm, colour focusing, Hales–Jewett, density versions, Rado, ultrafilters, algebraic lower-bound colourings, parameter sets, partition calculus.
- [Designs, codes and finite geometry](pure-math/designs-and-codes.md): Constructions and nonexistence proofs for designs, difference sets, Hadamard matrices, projective planes and codes: cyclic developments, multipliers, quadratic-form obstructions, recursive constructions, code bounds, MacWilliams and invariant theory.
- [Enumerative and algebraic combinatorics](pure-math/enumerative-combinatorics.md): Generating functions and their asymptotics, inversion formulas, counting up to symmetry, bijections, q-series, and algebra that constrains face numbers.
- [Structural graph theory](pure-math/structural-graph-theory.md): Colouring and structure arguments for graphs: discharging, recolouring, orientations, minors and decompositions, min–max duality, and explicit lifts of small graphs.
- [Analytic number theory](pure-math/analytic-number-theory.md): Primes and arithmetic functions by complex analysis, exponential and character sums, mean values, zero density, multiplicative functions and explicit estimates.
- [Sieve methods](pure-math/sieve-methods.md): Upper and lower bounds for sifted sets: combinatorial and Λ² sieves, multidimensional weights, the parity barrier and how to break it, large sieves, and covering congruences.
- [Algebraic number theory and Diophantine equations](pure-math/diophantine-equations.md): Local and global obstructions, descent, factorization in number rings, p-adic methods, rational points on curves, the modular method, effective bounds that end in a finite search, and multiplicative-function equations.
- [Diophantine approximation and transcendence](pure-math/diophantine-approximation.md): Irrationality and transcendence proofs, auxiliary polynomials and functions, linear forms in logarithms, the subspace theorem, and potential theory for algebraic integers.
- [Modular forms and automorphic methods](pure-math/modular-forms.md): Finite checks of q-series identities, small spaces of modular forms, Hecke operators, congruences, exact formulas, trace formulas, mock modular forms, automorphy, and modular forms as extremal auxiliary functions.
- [Groups, rings, fields and representations](pure-math/algebra.md): Proof techniques of algebra: group actions, characters, transfer, free and geometric group theory, Galois theory, rings by idempotents and localization.
- [Algebraic geometry](pure-math/algebraic-geometry.md): Algebraic geometry and commutative algebra as proof tools: reduction mod p, transfer between fields, finiteness, intersection and dimension counts, point counts over finite fields, real roots.
- [Homological and categorical methods](pure-math/homological-methods.md): Spectral sequences, representability, derived functors, sheaf and group cohomology as obstructions, categorification, representation and homological stability.
- [Inequalities and estimation](pure-math/inequalities-and-estimation.md): Classical inequalities and the working tricks of estimation: convexity, Cauchy–Schwarz, Hölder, majorization, geometric and functional inequalities, dyadic pigeonholing, amplification, tensor powers.
- [Real and harmonic analysis](pure-math/harmonic-analysis.md): Fourier methods, decompositions and maximal functions, oscillatory integrals, restriction and Kakeya, dimension theory, approximation and limits of sequences.
- [Functional analysis](pure-math/functional-analysis.md): Banach and Hilbert space principles, compactness, extreme points, spectral theory, fixed-point theorems, variational principles, amenability, exotic spaces, free probability.
- [PDE, calculus of variations and geometric analysis](pure-math/pde-and-geometric-analysis.md): Energy and maximum-principle methods, regularity, variational and min–max existence, compactness and bubbling, symmetry, flexibility (convex integration, h-principle), geometric flows, curvature and index obstructions, optimal transport.
- [Complex analysis and asymptotics](pure-math/complex-analysis.md): Residues and contour shifts, zero counting, maximum modulus and growth, conformal and quasiconformal maps, value distribution, saddle-point asymptotics.
- [Topological methods](pure-math/topological-methods.md): Fixed-point, degree and equivariant arguments for combinatorics and analysis, obstruction theory, combinatorial topology, and the invariants of low- and high-dimensional topology.
- [Discrete and convex geometry](pure-math/discrete-geometry.md): Convexity theorems, incidences and drawings, rigidity, dissections, lattice points, tilings and lattice packings.
- [Logic, model theory and set theory](pure-math/logic-and-set-theory.md): Compactness and finite-to-infinite transfer, model-theoretic tools, independence, ordinals and well-quasi-orders, undecidability, definable combinatorics.
- [Probability theory](pure-math/probability.md): Tail bounds, concentration, couplings, comparison and interpolation, Boolean analysis, scaling limits, random models, and suprema of processes.
- [Information theory](pure-math/information-theory.md): Divergence inequalities, information lower bounds, entropy-region inequalities, entropy power and large deviations of empirical measures; entropy counting itself is in extremal combinatorics (T10235).
- [Statistical-mechanics methods](pure-math/statistical-mechanics.md): Proof methods from mathematical physics: contours, cluster expansions, integrable lattice models, Gaussian and Grassmann integrals, zero counting for random functions, and bootstrap bounds.
- [Combinatorial game theory](pure-math/combinatorial-games.md): Existence arguments for winning strategies, positional-game strategies, impartial and partizan game algebra, and periodicity results that turn a game into a finite check; game solving by search is T113–T117.
- [Dynamics and ergodic theory](pure-math/dynamics-and-ergodic-theory.md): Ergodic Ramsey theory, structure and rigidity of measure-preserving actions, recurrence, symbolic coding and shadowing, KAM, renormalization, transfer operators, and topological arguments for one- and two-dimensional dynamics.

**Algorithms**
- [Reductions and hardness](algorithms/reductions-and-hardness.md): Reductions as tools and as judges: NP-, #P-, fine-grained and parameterized hardness, PCP, and where a goal sits in the arithmetical hierarchy.
- [Barriers](algorithms/barriers.md): Results that prove a class of methods cannot reach a target: relativization, natural proofs, algebrization, locality, extension complexity, integrality gaps, rigidity.
- [Proof complexity](algorithms/proof-complexity.md): Predicts how large a certificate in a given proof system must be, which proof system a solver simulates, and how to certify parity reasoning.
- [Query and decision-tree complexity](algorithms/query-complexity.md): Lower and exact bounds on how many probes, comparisons or queries any algorithm needs.
- [Communication complexity](algorithms/communication-complexity.md): Lower bounds on the bits two or more parties must exchange, and their uses for circuits, LPs and matrices.
- [Circuit and algebraic complexity](algorithms/circuit-and-algebraic-complexity.md): Lower bounds for Boolean and algebraic circuits, the matrix-multiplication exponent, and arithmetization.
- [Quantum methods](algorithms/quantum-methods.md): Quantum detours for classical statements, bounds on quantum strategies, nonlocal games as reductions, and codes from group complexes.
- [Boolean functions and pseudorandomness](algorithms/boolean-functions-and-pseudorandomness.md): Fourier analysis on the cube, juntas and thresholds, extractors, list decoding, multiplicative weights, weak regularity and spread approximations.
- [Derandomization and constructive existence](algorithms/derandomization.md): Turns random constructions into deterministic ones, judges when that is possible, and counts partial solutions to prove existence.
- [Spectral methods and expanders](algorithms/spectral-methods.md): Lovász theta, expander constructions, spectral sparsifiers, planted-structure recovery and high-dimensional expanders.
- [Relaxations, rounding and decomposition](algorithms/relaxations-and-decomposition.md): Operations-research tools: rounding fractional solutions, column generation, Lagrangian and Benders decomposition, matroid intersection, submodular selection, polyhedral computation.
- [Certificates from algorithms](algorithms/certificates-from-algorithms.md): Algorithm-side ways to make outputs checkable or cross-checked: prepared proofs, closed-set certificates, orbit representatives, double generation.
- [Generation and classification](algorithms/generation-and-classification.md): Enumeration methods beyond canonical augmentation (T30): homomorphism chains, reverse search, refinement filters, specialized generators, code and design classification.
- [Symmetry reduction in search](algorithms/symmetry-reduction.md): Symmetry tools beyond static breaking and prescribed groups (T24–T29): dynamic breaking, orbitopes, move-order reduction, abstraction.
- [Tree and state-space search](algorithms/tree-search.md): Branch and bound, heuristic and frontier search, run-size estimation, restarts, parallel load balancing, and Ramsey and design case splits.
- [Constraint propagation](algorithms/constraint-propagation.md): Filtering inside CP and subgraph solvers: arc consistency, matching-based alldifferent, table constraints, lazy clause generation, invariant filtering.
- [Counting and dynamic programming](algorithms/counting-and-dynamic-programming.md): Exact counting and optimization algorithms: subset DP, transforms over subsets, algebraic sieving, transfer matrices, decision diagrams, convolution, approximate counting.
- [Parameterized and exact exponential algorithms](algorithms/parameterized-algorithms.md): Kernels, compression, colour coding, width-based DP and branching analysis, used as structure detectors and preprocessors.
- [Meet in the middle, tables and bit tricks](algorithms/meet-in-the-middle-and-tables.md): Speed and memory tricks for exhaustive runs: split searches, hashing, precomputed tables, ranking, Bloom filters, bit parallelism.
- [Heuristic search for constructions](algorithms/construction-heuristics.md): Rollout, tree-sampling and neighbourhood methods for find and bound problems, beyond the computation area's local search (T90–T100).

**Computation**
- [SAT solving and clausal proofs](computation/sat-solving.md): SAT solvers on CNF encodings, and the UNSAT proofs (DRAT, LRAT, PR) that make their answers checkable.
- [Constraint and SMT solving](computation/constraint-solving.md): SMT with Lean replay, constraint programming, answer set programming, model checking.
- [Automated reasoning and decision procedures](computation/automated-reasoning.md): first-order provers, finite model finders, e-graphs, Walnut, CAD and termination provers outside Lean.
- [Symmetry reduction and isomorph-free generation](computation/symmetry-and-generation.md): symmetry breaking, prescribed automorphisms, coset decomposition, canonical generation, SAT Modulo Symmetries.
- [Exhaustive search and case analysis](computation/exhaustive-search.md): exact cover, hitting sets, gluing with LP pruning, branch-and-bound over types, decider portfolios, orbit counting.
- [Number-theoretic computation](computation/number-theoretic-computation.md): Diophantine and curve search, sieves, factoring, number-theory CAS, LLL and BKZ, primality certificates.
- [Linear and integer programming bounds](computation/linear-and-integer-programming.md): LP dual certificates, exact MIP certificates, Delsarte LP bounds, Lagrangian duality, large-scale solvers.
- [Semidefinite and sum-of-squares relaxations](computation/semidefinite-and-sos.md): SDP bounds for codes, SOS and Positivstellensatz, flag algebras, moment and copositive hierarchies, Lyapunov synthesis.
- [Computer algebra](computation/computer-algebra.md): Gröbner bases, Nullstellensatz cofactors, creative telescoping and WZ, sequence guessing, coset enumeration.
- [Rigorous numerics and computer-assisted analysis](computation/rigorous-numerics.md): interval and ball arithmetic, Newton-type existence tests, validated ODEs, quadrature, spectra, Conley index, CAP for PDE.
- [Experimental mathematics](computation/experimental-mathematics.md): PSLQ, symbolic calculators, OEIS, databases, automated conjecturing, persistent homology, judging numerical evidence.
- [Machine learning for conjectures](computation/machine-learning-for-conjectures.md): supervised learning with attribution, database statistics, symbolic regression, interpretability.
- [Metaheuristic and local search](computation/local-search.md): annealing, seeded repair, flip graphs, evolutionary, memetic, quality-diversity, CMA-ES, swarms, basin hopping, tuning.
- [Learned generative search](computation/learned-search.md): cross-entropy method, PatternBoost, trained oracles, AlphaTensor-style games, RL for move sequences.
- [Program search and synthesis](computation/program-search.md): FunSearch, AlphaEvolve, OpenEvolve, CEGIS, library learning, invariant learning.
- [Game solving](computation/game-solving.md): retrograde analysis, proof-number and alpha-beta search, domain pruning, strategy trees as certificates.
- [Certificate design for Lean's kernel](computation/certificate-design.md): witnesses, verified reductions and checkers, kernel-friendly data, splitting, shrinking, exact rounding, randomized filters.
- [Lean tactics and automation](computation/lean-automation.md): axiom audit, linarith family, omega and lia, grind, Duper, Aesop, hammers, Canonical, Loogle, Plausible, theory exploration.
- [AI theorem proving and research assistants](computation/ai-theorem-proving.md): AlphaProof, AlphaGeometry, Aristotle, open neural provers, Lean Copilot, proof search methods, autoformalization, literature triage.
- [Formal libraries and infrastructure](computation/formal-libraries.md): Mathlib, the Isabelle AFP, blueprints, Formal Conjectures.
- [Hardware and scale](computation/hardware-and-scale.md): GPU and FPGA kernels, volunteer and grid computing, the one-PC sizing rule.

**Other fields**
- [Physics-style methods](other-fields/physics-style-methods.md): scaling, perturbation, random-model universality, mean-field and replica predictions, dualities, Noether, physics as a conjecture engine, measure first.
- [Engineering and design methods](other-fields/engineering-and-design.md): TRIZ, ideal final result, morphological analysis, design of experiments, bottlenecks, bisection, rubber duck, red teaming, pre-mortem, retrosynthesis.
- [Reasoning modes](other-fields/reasoning-modes.md): abduction, Fermi estimation, plausible and Bayesian reasoning, differential diagnosis, cribs.
- [Statistics of mathematical evidence](other-fields/statistics-of-evidence.md): small-number traps, null models, multiple comparisons, extrapolation, rare-event and exact sampling, plots, pre-registration.
- [Research practice and philosophy of proof](other-fields/research-practice.md): proofs and refutations, research programmes, anomalies, risky predictions, rising sea, partial progress, literature archaeology, what counts as proof.
- [Choosing problems and allocating effort](other-fields/effort-allocation.md): problems with an attack, a dozen problems, prize lists, bandits, value of information, calibrated forecasts, stopping rules.
- [Collaboration and shared testing](other-fields/collaboration.md): Polymath, adversarial collaboration, blind benchmarks, citizen-science games.
- [Creativity methods](other-fields/creativity-methods.md): lateral thinking, random stimulus, synectics, SCAMPER, bisociation, Oblique Strategies, six hats, hands-on play.
- [Deadlock breakers](other-fields/deadlock-breakers.md): neighbour problems, weaker tools, root causes, the other truth value, richer models, near-misses, tight numerics, outsiders, elementary tools, stepping away.

**Breakthroughs**
- [Checking decides what counts](breakthroughs/checking-decides-what-counts.md): formalization and re-verification settle a proof's status; an uncheckable proof does not count.
- [The conjecture was false](breakthroughs/conjecture-was-false.md): "obviously true" conjectures broke to an explicit object or a witness-free disproof.
- [Experiment finds the object](breakthroughs/experiment-finds-the-object.md): play, simulation, numerics and blind benchmarks found the object a checker then confirmed.
- [Failure as information, and a changed angle](breakthroughs/failure-and-a-changed-angle.md): a failed step named what to change; long attacks ended with a new angle.
- [Finite reduction, then a certificate](breakthroughs/finite-reduction-then-certificate.md): theory cut the problem to finitely many cases; search or SAT settled them with a checkable certificate.
- [An imported tool](breakthroughs/imported-tool.md): a technique native to another field, often carried in by outsiders.
- [An overlooked simple tool](breakthroughs/overlooked-simple-tool.md): an old elementary theorem succeeded where heavy machinery stalled.
- [Physics predicts, mathematics proves](breakthroughs/physics-predicts.md): a heuristic prediction fixed the exact target years before the proof.
- [A reformulation first](breakthroughs/reformulation-first.md): an equivalent or stronger restatement in another language made the problem attackable.
