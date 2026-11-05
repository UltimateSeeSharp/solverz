# PDE, calculus of variations and geometric analysis
Energy and maximum-principle methods, regularity, variational and min–max existence, compactness and bubbling, symmetry, flexibility (convex integration, h-principle), geometric flows, curvature and index obstructions, optimal transport.

### T670 Energy methods, conservation laws, monotonicity formulae
`prove` `bound` · stage: argue · signals: pde, inequality
aka: energy estimates, conserved quantities, monotonicity formulae, Gronwall, long-time existence, blow-up criteria, Morawetz estimates
- What: find a conserved or monotone quantity that controls the solution for all time.
- Fits when: evolution equations; long-time existence or blow-up.
- Lean: a hand proof; Mathlib has Gronwall's inequality (`Analysis/ODE/Gronwall.lean`) for the ODE step.
- Example: energy estimates and monotonicity formulae in the Tricki article ([Tricki: conservation laws and monotonicity formulae](https://www.tricki.org/article/Use_conservation_laws_and_monotonicity_formulae_to_obtain_long-time_control_on_solutions)).
- See also: T330, T686, T679

### T671 Maximum principle and comparison
`prove` · stage: argue · signals: pde, analytic, inequality
aka: weak and strong maximum principle, Hopf lemma, comparison principle, sub- and supersolutions, positivity, uniqueness, a priori bounds, harmonic functions
- What: solutions of elliptic or parabolic inequalities attain extrema on the boundary; sub- and supersolutions sandwich solutions.
- Fits when: uniqueness, positivity, a priori bounds for second-order equations.
- Lean: Mathlib has the holomorphic maximum modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`); the PDE version not found.
- Example: harmonic functions attain their maxima on the boundary; Hopf's strong maximum principle ([Wikipedia: Maximum principle](https://en.wikipedia.org/wiki/Maximum_principle)).
- See also: T681, T682, T698

### T672 Harnack inequalities
`prove` `bound` · stage: argue · signals: pde, inequality
aka: Harnack's inequality, Li–Yau gradient estimate, Hamilton's Harnack, positive solutions, Liouville theorems, regularity
- What: positive solutions are comparable at nearby points.
- Fits when: regularity, Liouville theorems, convergence of solutions.
- Lean: — (not found in Mathlib).
- Example: Harnack's inequality for harmonic functions; Li–Yau and Hamilton's versions for flows ([Wikipedia: Harnack's inequality](https://en.wikipedia.org/wiki/Harnack's_inequality)).
- See also: T673, T686

### T673 De Giorgi–Nash–Moser iteration
`prove` · stage: argue · signals: pde, inequality
aka: De Giorgi iteration, Moser iteration, Nash, level-set truncation, Hölder continuity, measurable coefficients, Hilbert's 19th problem
- What: iterate energy inequalities on shrinking level sets to gain boundedness and Hölder continuity with rough coefficients.
- Fits when: regularity of weak solutions with merely measurable coefficients.
- Lean: —
- Example: the solution of Hilbert's 19th problem ([Wikipedia: Hilbert's nineteenth problem](https://en.wikipedia.org/wiki/Hilbert's_nineteenth_problem)).
- See also: T317, T674, T672

### T674 Schauder estimates and bootstrapping
`prove` · stage: argue · signals: pde
aka: Schauder theory, Hölder spaces, elliptic regularity, bootstrapping regularity, gain two derivatives, smoothness of nonlinear solutions
- What: Hölder regularity of the data gives two more derivatives of the solution; iterate.
- Fits when: smoothness of solutions to nonlinear elliptic equations once a base regularity holds.
- Lean: — (Schauder estimates not found in Mathlib).
- Example: Schauder theory for elliptic equations ([Wikipedia: Schauder estimates](https://en.wikipedia.org/wiki/Schauder_estimates)).
- See also: T673, T321

### T675 Galerkin approximation
`prove` · stage: argue · signals: pde, analytic
aka: Galerkin method, Faedo–Galerkin, finite-dimensional approximations, uniform bounds, weak limits, weak solutions of evolution equations
- What: solve in finite-dimensional subspaces, get uniform bounds, pass to a weak limit.
- Fits when: existence of weak solutions to evolution equations.
- Lean: — (not found in Mathlib).
- Example: weak solutions of linear and nonlinear evolution equations via Galerkin schemes ([Wikipedia: Galerkin method](https://en.wikipedia.org/wiki/Galerkin_method)).
- See also: T656, T660

### T676 Direct method of the calculus of variations
`prove` · stage: argue · signals: pde, analytic
aka: direct method, coercivity, lower semicontinuity, weak compactness, minimizers, Dirichlet's principle, Tonelli
- What: coercivity, lower semicontinuity and compactness give a minimizer.
- Fits when: existence of minimizers of convex-type functionals.
- Lean: Mathlib: `LowerSemicontinuousOn.exists_isMinOn`; the Sobolev-space setting is not there.
- Example: Dirichlet's principle made rigorous ([Wikipedia: Direct method](https://en.wikipedia.org/wiki/Direct_method_in_the_calculus_of_variations)).
- See also: T656, T677, T317

### T677 Mountain pass and min–max critical points
`prove` `find` · stage: argue · signals: pde, analytic, topology
aka: mountain pass theorem, Ambrosetti–Rabinowitz, Palais–Smale condition, saddle points, minimax principle, deformation lemma, non-minimizing solutions
- What: a functional with mountain-pass geometry and Palais–Smale compactness has a saddle critical point.
- Fits when: existence of non-minimizing solutions.
- Lean: — (not found in Mathlib).
- Example: Ambrosetti–Rabinowitz mountain pass theorem ([Wikipedia: Mountain pass theorem](https://en.wikipedia.org/wiki/Mountain_pass_theorem)).
- See also: T678, T717, T665

### T678 Min–max over sweepouts (Almgren–Pitts)
`prove` `find` · stage: argue · signals: manifold, pde, topology
aka: Almgren–Pitts min–max, sweepouts, minimal hypersurfaces, Morse index, Willmore conjecture, Marques–Neves
- What: find minimal surfaces as min–max over families of surfaces with topological nontriviality.
- Fits when: existence and index of minimal hypersurfaces; geometric extremal problems.
- Lean: —
- Example: the Marques–Neves proof of the Willmore conjecture ([arXiv:1202.6036](https://arxiv.org/abs/1202.6036)).
- See also: T677, T716

### T679 Concentration compactness and bubbling
`prove` · stage: argue · signals: pde, analytic
aka: concentration-compactness principle, Lions, profile decomposition, bubbles, loss of compactness under scaling, critical exponents, Yamabe problem, Aubin–Schoen
- What: a minimizing sequence converges, vanishes or splits; rule out the bad cases or extract bubbles.
- Fits when: critical exponents; loss of compactness under scaling.
- Lean: —
- Example: Lions' concentration-compactness principle; Aubin–Schoen solution of the Yamabe problem ([Wikipedia: Pierre-Louis Lions](https://en.wikipedia.org/wiki/Pierre-Louis_Lions), [Wikipedia: Yamabe problem](https://en.wikipedia.org/wiki/Yamabe_problem)).
- See also: T676, T656

### T680 Scaling identities for nonexistence (Pohozaev, Derrick)
`prove` · stage: argue · signals: pde, impossibility
aka: Pohozaev identity, Derrick's theorem, virial identity, multiply by x·∇u, rescaling argument, supercritical nonexistence, static solitons
- What: test the equation against x·∇u or a rescaling to get an identity that forbids solutions.
- Fits when: nonexistence of solutions or stationary solitons above critical exponents.
- Lean: —
- Example: Derrick's theorem: no stable static solitons in dimension ≥ 3 for scalar fields ([Wikipedia: Derrick's theorem](https://en.wikipedia.org/wiki/Derrick's_theorem)).
- See also: T621, T679

### T681 Moving planes
`prove` · stage: argue · signals: pde, geometry, symmetric
aka: method of moving planes, Alexandrov reflection, Gidas–Ni–Nirenberg, radial symmetry, Serrin's problem, maximum principle
- What: reflect across planes and push the plane until symmetry is forced by the maximum principle.
- Fits when: proving solutions are radially symmetric.
- Lean: —
- Example: the Gidas–Ni–Nirenberg symmetry theorem ([Wikipedia: Louis Nirenberg](https://en.wikipedia.org/wiki/Louis_Nirenberg)).
- See also: T671, T613

### T682 Viscosity solutions
`prove` · stage: argue · signals: pde
aka: Crandall–Lions viscosity solutions, test functions touching from above and below, Hamilton–Jacobi equations, fully nonlinear equations, comparison principle, stability under limits
- What: define solutions by touching test functions; they are stable under limits and unique by comparison.
- Fits when: fully nonlinear first- or second-order equations without classical solutions.
- Lean: — (not found in Mathlib).
- Example: Crandall–Lions theory of Hamilton–Jacobi equations ([Wikipedia: Viscosity solution](https://en.wikipedia.org/wiki/Viscosity_solution)).
- See also: T671, T689

### T683 Carleman estimates (unique continuation)
`prove` · stage: argue · signals: pde, inequality
aka: Carleman estimates, unique continuation, weighted inequalities, observability, control theory, inverse problems
- What: weighted inequalities show that solutions vanishing on an open set vanish everywhere.
- Fits when: uniqueness and control problems.
- Lean: —
- Example: Carleman's unique continuation theorem ([Wikipedia: Torsten Carleman](https://en.wikipedia.org/wiki/Torsten_Carleman)).
- See also: T321, T706

### T684 Convex integration
`find` `prove` · stage: construct · signals: pde, manifold, construction
aka: convex integration, Nash–Kuiper, oscillatory corrections, Onsager's conjecture, Isett, De Lellis–Székelyhidi, differential inclusions, non-uniqueness, wild solutions
- What: build solutions by adding highly oscillatory corrections that fix the error at each step.
- Fits when: flexible, non-unique, low-regularity solutions (isometric embeddings, fluids).
- Lean: —
- Example: Nash–Kuiper C¹ isometric embeddings; Isett's proof of Onsager's conjecture; De Lellis–Székelyhidi Euler as a differential inclusion ([Wikipedia: Nash–Kuiper theorem](https://en.wikipedia.org/wiki/Nash–Kuiper_theorem), [arXiv:1608.08301](https://arxiv.org/abs/1608.08301), [arXiv:math/0702079](https://arxiv.org/abs/math/0702079)).
- See also: T685

### T685 h-principle
`find` `prove` · stage: argue · signals: topology, manifold, construction
aka: homotopy principle, Gromov's h-principle, flexibility, formal solutions, open differential relations, Smale's sphere eversion, immersions
- What: formal (homotopy-theoretic) solutions deform to genuine ones for open, flexible relations.
- Fits when: immersions and embeddings with differential conditions.
- Lean: —
- Example: Smale's sphere eversion; Gromov's h-principle ([Wikipedia: Homotopy principle](https://en.wikipedia.org/wiki/Homotopy_principle)).
- See also: T684, T730

### T686 Geometric flows with monotone quantities and surgery
`prove` · stage: argue · signals: manifold, pde, topology, classification
aka: Ricci flow, Perelman entropy, mean curvature flow, heat-type flows, diffusion and geometric flows, surgery, cut out the singularity and continue, Poincaré conjecture, geometrization
- What: deform the geometry by a heat-type flow; a monotone entropy controls singularities, and surgery cuts them out so the flow continues.
- Fits when: classification and uniformization of manifolds; a flow or iteration works except at rare blow-ups.
- Lean: —
- Example: Perelman's proof of the Poincaré and geometrization conjectures via Ricci flow with surgery; Hamilton's flow imitates the heat equation ([arXiv:math/0211159](https://arxiv.org/abs/math/0211159), [Wikipedia: Ricci flow](https://en.wikipedia.org/wiki/Ricci_flow), [Poincaré conjecture](https://en.wikipedia.org/wiki/Poincar%C3%A9_conjecture)).
- See also: T670, T330, T672

### T687 Calibrations
`prove` · stage: argue · signals: manifold, inequality
aka: calibrated geometry, Harvey–Lawson, closed forms bounding volume, volume minimizing submanifolds, complex submanifolds of Kähler manifolds, special Lagrangians
- What: a closed form bounding volume on all competitors and attained on a surface proves that surface minimizing.
- Fits when: proving specific submanifolds are volume minimizing.
- Lean: —
- Example: Harvey–Lawson calibrated geometries: complex submanifolds of Kähler manifolds minimize volume ([Wikipedia: Calibrated geometry](https://en.wikipedia.org/wiki/Calibrated_geometry)).
- See also: T316, T678

### T688 Integrability (Lax pairs, inverse scattering)
`compute` `prove` · stage: argue · signals: pde, exact-value
aka: Lax pairs, inverse scattering transform, solitons, KdV, nonlinear Schrödinger, integrable systems, scattering data
- What: map the nonlinear flow to a linear evolution of scattering data.
- Fits when: KdV, NLS and other integrable equations.
- Lean: —
- Example: exact solution of KdV by inverse scattering ([Wikipedia: Inverse scattering transform](https://en.wikipedia.org/wiki/Inverse_scattering_transform)).
- See also: T802, T689

### T689 Method of characteristics
`compute` `prove` · stage: argue · signals: pde, dynamics
aka: characteristic curves, first-order PDE, transport equations, Hamilton–Jacobi, shocks, Burgers equation, reduction to ODE
- What: reduce a first-order PDE to ODEs along characteristic curves.
- Fits when: transport and Hamilton–Jacobi equations; shocks.
- Lean: the ODE step via Mathlib's `IsPicardLindelof`; the PDE reduction by hand.
- Example: solving first-order quasilinear PDE ([Wikipedia: Method of characteristics](https://en.wikipedia.org/wiki/Method_of_characteristics)).
- See also: T661, T682

### T690 Bochner technique
`prove` · stage: argue · signals: manifold, impossibility
aka: Bochner's formula, Weitzenböck formula, vanishing theorems, harmonic forms, positive Ricci curvature, parallel tensors
- What: a Weitzenböck formula plus a curvature sign forces harmonic objects to be parallel or zero.
- Fits when: vanishing theorems in Riemannian geometry.
- Lean: — (Riemannian curvature not found in Mathlib).
- Example: Bochner's theorem: positive Ricci curvature kills harmonic 1-forms ([Wikipedia: Bochner's formula](https://en.wikipedia.org/wiki/Bochner's_formula)).
- See also: T693, T691

### T691 Comparison geometry
`prove` `bound` · stage: argue · signals: manifold, inequality
aka: Bishop–Gromov volume comparison, Toponogov's theorem, Rauch comparison, model spaces of constant curvature, curvature bounds, CAT(k)
- What: compare volumes or triangles with model spaces of constant curvature.
- Fits when: curvature bounds imply topology or volume bounds.
- Lean: —
- Example: Bishop–Gromov volume comparison; Toponogov's triangle comparison ([Wikipedia: Bishop–Gromov inequality](https://en.wikipedia.org/wiki/Bishop–Gromov_inequality), [Wikipedia: Toponogov's theorem](https://en.wikipedia.org/wiki/Toponogov's_theorem)).
- See also: T690, T318

### T692 Minimal surfaces or spinors as probes
`prove` · stage: argue · signals: manifold, pde, inequality
aka: Schoen–Yau minimal hypersurfaces, Witten spinor proof, Dirac operator, positive mass theorem, positive energy theorem, scalar curvature
- What: use minimal hypersurfaces (Schoen–Yau) or Dirac operators (Witten) to detect positivity of mass or curvature.
- Fits when: scalar curvature and general relativity problems.
- Lean: —
- Example: the positive energy theorem ([Wikipedia: Positive energy theorem](https://en.wikipedia.org/wiki/Positive_energy_theorem)).
- See also: T693, T678

### T693 Index theory as an obstruction
`prove` · stage: argue · signals: manifold, topology, pde, impossibility
aka: Atiyah–Singer index theorem, analytic index, topological index, Â-genus, positive scalar curvature obstructions, counting solutions
- What: the analytic index equals a topological one; a nonzero index forces solutions, vanishing theorems force zero index.
- Fits when: metrics of positive scalar curvature; counting solutions.
- Lean: — (not found in Mathlib).
- Example: the Atiyah–Singer index theorem and the Â-genus obstruction ([Wikipedia: Atiyah–Singer index theorem](https://en.wikipedia.org/wiki/Atiyah–Singer_index_theorem)).
- See also: T659, T719, T690

### T694 Pseudoholomorphic curves
`prove` · stage: argue · signals: manifold, topology
aka: J-holomorphic curves, Gromov compactness, symplectic rigidity, non-squeezing, Gromov–Witten invariants, symplectic embeddings
- What: count or produce J-holomorphic curves to get symplectic rigidity.
- Fits when: symplectic embedding and fixed-point questions.
- Lean: —
- Example: Gromov's non-squeezing theorem ([Wikipedia: Non-squeezing theorem](https://en.wikipedia.org/wiki/Non-squeezing_theorem)).
- See also: T718

### T695 Optimal transport
`prove` `bound` · stage: argue · signals: analytic, geometry, inequality
aka: Monge–Kantorovich, Kantorovich duality, Wasserstein distance, Brenier map, displacement convexity, sharp Sobolev inequalities, Brunn–Minkowski by transport
- What: move one measure to another at minimal cost; the optimal map and Kantorovich duality give sharp functional and geometric inequalities.
- Fits when: Sobolev, isoperimetric or Brunn–Minkowski-type inequalities; Wasserstein distances.
- Lean: — (optimal transport not found in Mathlib).
- Example: Cordero-Erausquin–Nazaret–Villani's sharp Sobolev inequalities by transport, extended by Kristály to Ric ≥ 0 ([arXiv:2307.03527](https://arxiv.org/abs/2307.03527), [Wikipedia: Transportation theory](https://en.wikipedia.org/wiki/Transportation_theory_%28mathematics%29)).
- See also: T611, T615, T613

### T843 Minimize within a symmetry class
`find` `prove` · stage: argue · signals: pde, dynamics, symmetric, construction
aka: equivariant minimizers, principle of symmetric criticality, Palais, G-equivariant loops, symmetric loop space, choreographies, figure-eight orbit, Chenciner–Montgomery, Ferrario–Terracini, Marchal's averaging, collision exclusion, periodic orbits of the n-body problem
- What: restricts an invariant functional to the objects fixed by a symmetry group G and minimizes there; by Palais's principle a critical point of the restriction is a critical point of the full functional, and the symmetry also shapes the minimizer and can exclude degenerate ones.
- Fits when: a symmetric periodic orbit or solution of a variational problem is wanted and the direct method (T676) fails on the full space: no coercivity, or minimizers that are trivial or collide; choose G so the restricted problem is coercive and its minimizers avoid the bad set.
- Lean: as T676 for the minimization (`LowerSemicontinuousOn.exists_isMinOn`); Mathlib has no Sobolev loop spaces and no principle of symmetric criticality.
- Example: Chenciner–Montgomery proved the figure-eight three-body orbit exists by a variational method ([arXiv:math/0011268](https://arxiv.org/abs/math/0011268)); Ferrario–Terracini: the action on G-equivariant loops is coercive exactly when G fixes no nonzero configuration, and under a condition on G its minimizers are collision-free (Marchal's averaging, blow-up), which recovers the eight and finds new orbits ([arXiv:math-ph/0302022](https://arxiv.org/abs/math-ph/0302022)); the principle holds for compact G and can fail otherwise ([arXiv:1011.3429](https://arxiv.org/abs/1011.3429)).
- See also: T676, T1306, T27
