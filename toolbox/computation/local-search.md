# Metaheuristic and local search
Heuristic search over discrete objects or real coordinates for find and bound problems; only the final object is checked.

### T90 Simulated annealing and tabu search
`find` `bound` · stage: local-search · signals: set-family, colouring, construction, near-miss
aka: annealing, temperature schedule, tabu search, Metropolis moves, covering designs, packing designs, La Jolla Covering Repository, colourings, codes
- What: random moves accepted with a temperature-dependent probability.
- Fits when: covering and packing designs, colourings, codes (find and bound).
- Lean: the property checked by `decide` over packed t-subsets (T121).
- Example: Nurmela–Östergård's annealing found many of the best covering designs ([covering design](https://en.wikipedia.org/wiki/Covering_design); [LJCR](https://dmgordon.org/covering-designs/)).
- See also: T2, T91, T94, T98

### T91 Local search seeded by algebraic colourings
`find` · stage: local-search · signals: colouring, graph, construction, near-miss
aka: Paley colouring, cubic colouring, Paley graph, algebraic seeds, repair search, Ramsey lower bounds, Exoo
- What: starts from Paley or cubic colourings and repairs them locally.
- Fits when: Ramsey lower bounds and other avoidance colourings.
- Lean: check that no k-subset is monochromatic with bitset cliques (T121); C(n,k) grows fast, so keep n·k modest.
- Example: 28 new lower bounds for classical Ramsey numbers, some from the Paley colouring of K₁₀₁ ([Exoo–Tatarevic](https://arxiv.org/abs/1504.02403)).
- See also: T27, T90

### T92 Random walks on flip graphs
`find` `bound` · stage: local-search · signals: matrix, product-structure, construction
aka: flip graphs, matrix multiplication schemes, bilinear complexity, tensor rank, Strassen-type schemes, (4,4,5), (5,5,5), fewer multiplications
- What: local moves between valid schemes, plus reductions.
- Fits when: bilinear and tensor-rank upper bounds; any "scheme" whose validity is an identity.
- Lean: the scheme is a polynomial identity, checked by `ring` (or `decide` over GF(2)).
- Example: fewer multiplications for (4,4,5) and (5,5,5) matrix products ([Kauers–Moosbauer](https://arxiv.org/abs/2212.01175)).
- See also: T104, T108

### T93 Evolutionary and genetic search
`find` `bound` · stage: local-search · signals: construction
aka: genetic algorithms, island model, populations, migration, selection, formula search, program search
- What: selection over a population, with migration between islands.
- Fits when: rugged search spaces; formula and program search.
- Lean: check the final object only.
- Example: FunSearch's islands ([FunSearch](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC10794145/fullTextXML)); PySR's multi-population symbolic regression ([PySR](https://arxiv.org/abs/2305.01582)).
- See also: T94, T95, T107

### T94 Memetic algorithms
`find` `bound` · stage: local-search · signals: sequence, construction
aka: hybrid genetic and local search, memetic-tabu, low-autocorrelation binary sequences, LABS, merit factor
- What: a population method whose individuals are improved by local search each generation.
- Fits when: combinatorial find or bound problems where crossover alone is too coarse.
- Lean: check the final object (T118).
- Example: memetic-tabu solvers for low-autocorrelation binary sequences (merit factor) ([arXiv:1406.5301](https://arxiv.org/abs/1406.5301); [Wikipedia: Memetic algorithm](https://en.wikipedia.org/wiki/Memetic_algorithm)).
- See also: T39, T90, T93

### T95 Quality-diversity search
`find` `bound` · stage: local-search · signals: construction
aka: MAP-Elites, novelty search, behaviour descriptors, deceptive objectives, diversity archive
- What: keeps the best solution in each cell of a grid of behaviour descriptors instead of one global best; diversity escapes deceptive objectives.
- Fits when: find or bound landscapes where the best objects look unlike the greedy ones.
- Lean: check the final object (T118).
- Example: Mouret–Clune's MAP-Elites ([arXiv:1504.04909](https://arxiv.org/abs/1504.04909)); OpenEvolve uses it inside ([OpenEvolve](https://github.com/codelion/openevolve)).
- See also: T93, T109

### T96 CMA-ES
`find` `bound` · stage: local-search · signals: analytic, geometry, construction
aka: covariance matrix adaptation, evolution strategies, derivative-free optimization, black-box optimization, packings, autocorrelation constants, function constructions
- What: samples candidates from a Gaussian and adapts its covariance toward successful steps; robust derivative-free optimization in tens to hundreds of dimensions.
- Fits when: continuous constructions with noisy or non-smooth scores (packings, autocorrelation constants, function constructions).
- Lean: snap to exact coordinates first (T99, T124).
- Example: Hansen's tutorial ([arXiv:1604.00772](https://arxiv.org/abs/1604.00772); [Wikipedia: CMA-ES](https://en.wikipedia.org/wiki/CMA-ES)).
- See also: T98, T99

### T97 Swarm methods
`find` · stage: local-search · signals: graph, construction
aka: ant colony optimization, pheromone trails, particle swarm optimization, PSO, travelling salesman, tours, paths
- What: many simple agents share information through pheromone trails or best-position attraction.
- Fits when: path- or tour-like constructions (ants) and continuous search (particles).
- Lean: check the final object (T118).
- Example: Dorigo's ant system on the travelling salesman problem ([Wikipedia: Ant colony optimization algorithms](https://en.wikipedia.org/wiki/Ant_colony_optimization_algorithms)); Kennedy–Eberhart's PSO ([Wikipedia: Particle swarm optimization](https://en.wikipedia.org/wiki/Particle_swarm_optimization)).
- See also: T93, T96

### T98 Basin hopping
`find` `bound` · stage: local-search · signals: geometry, analytic, construction
aka: Monte Carlo minimization, perturb and minimize, energy landscapes, Lennard-Jones clusters, point configurations, packings, potentials
- What: perturbs, minimizes locally, then accepts or rejects by energy; the landscape becomes a staircase of local minima.
- Fits when: find or bound over tens to hundreds of real coordinates (point configurations, packings, potentials) with a cheap score.
- Lean: snap to exact coordinates first (T99).
- Example: Wales–Doye found the lowest known Lennard-Jones clusters up to 110 atoms ([arXiv:cond-mat/9803344](https://arxiv.org/abs/cond-mat/9803344)).
- See also: T51, T90, T96, T99

### T99 Continuous optimization with exact rounding
`find` `bound` · stage: local-search · signals: geometry, construction, numeric-only
aka: snap to rationals, exact coordinates, kissing configurations, sphere packings, Heilbronn problem, kissing number in 11 dimensions
- What: optimizes numerically, then snaps to exact rational or integer coordinates and re-verifies.
- Fits when: packings, kissing configurations, Heilbronn-type problems.
- Lean: exact inner products and norms by `norm_num`/`decide`.
- Example: AlphaEvolve's 593-sphere kissing configuration in 11 dimensions ([DeepMind](https://deepmind.google/discover/blog/alphaevolve-a-gemini-powered-coding-agent-for-designing-advanced-algorithms/)).
- See also: T96, T98, T108, T124

### T100 Bayesian optimization and algorithm selection
`find` `compute` · stage: local-search
aka: surrogate models, hyperparameter tuning, SATzilla, solver portfolios, per-instance algorithm selection, encoding choice, solver flags
- What: a surrogate model of an expensive score chooses the next trial; per-instance selection picks the solver or encoding from a portfolio by instance features.
- Fits when: tuning a SAT encoding, solver flags or search hyperparameters costs hours per trial.
- Lean: — (it tunes the search, not the result).
- Example: SATzilla's portfolio-based selection won SAT competitions ([arXiv:1111.2249](https://arxiv.org/abs/1111.2249); [Wikipedia: Algorithm selection](https://en.wikipedia.org/wiki/Algorithm_selection)); Bayesian optimization of expensive simulations and hyperparameters ([Wikipedia: Bayesian optimization](https://en.wikipedia.org/wiki/Bayesian_optimization)).
- See also: T1, T154

### T155 Physical energy minimization (Surface Evolver)
`find` `bound` · stage: local-search · signals: geometry, pde, construction, numeric-only
aka: foam simulation, surface tension, soap films, minimal surfaces, Surface Evolver, Brakke, gradient descent on a mesh, mean-curvature flow, Kelvin problem, Weaire–Phelan structure, partitions of space, physical simulation as a find engine
- What: models a continuous extremal shape as a physical system (film, foam, elastic surface) stored as a simplicial complex and lets gradient descent on its energy relax a candidate to a nearby local minimum.
- Fits when: a `find` or `bound` problem over continuous shapes or partitions (least area, least energy); seed it with good guesses, since descent only reaches a nearby minimum, or relax the formulation to search globally.
- Lean: — for the simulation (floating point, mesh error); a record counts once its value is computed exactly or enclosed rigorously (T64), or an analytic comparison proves it.
- Example: Weaire and Phelan ran Surface Evolver's minimization from a good initial configuration and beat Kelvin's foam by 0.3% in area ([Oudet](https://membres-ljk.imag.fr/Edouard.Oudet/research/Kelvin/kelvin_n.php), [Brakke](https://kenbrakke.com/kelvin/kelvin.html)); Kusner and Sullivan proved analytically that it beats any foam with Kelvin's topology ([Brakke](https://kenbrakke.com/kelvin/kelvin.html)), though its optimality is unproven ([Wikipedia: Weaire–Phelan structure](https://en.wikipedia.org/wiki/Weaire%E2%80%93Phelan_structure)); a relaxed density formulation recovers Weaire–Phelan with no initial guess ([Oudet](https://membres-ljk.imag.fr/Edouard.Oudet/research/Kelvin/kelvin_n.php)); the program ([Wikipedia: Surface Evolver](https://en.wikipedia.org/wiki/Surface_Evolver)).
- See also: T98, T99, T1308, T64
