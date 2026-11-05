# Linear and integer programming bounds
LP and ILP bounds made exact: dual certificates, exact MIP certificates, Delsarte-type LP bounds, Lagrangian duality and large-scale solvers.

### T48 LP duality certificates
`bound` `prove` · stage: relax · signals: inequality, impossibility
aka: Farkas' lemma, Farkas certificates, dual solution, LP relaxation, infeasibility certificate, dual and algebraic certificates, Walker's LPs, subgraph-count identities, Ramsey numbers
- What: a dual solution proves the bound; round the floats to rationals and re-verify exactly; the same shape covers SOS Gram matrices, Nullstellensatz cofactors, WZ rational functions and flag-algebra PSD matrices.
- Fits when: every LP relaxation; any optimality or impossibility claim with a convex or algebraic relaxation.
- Lean: round the dual to rationals; small ones by `linarith` (simplex oracle, checked by `ring`), large ones as a supplied dual checked by `norm_num`.
- Example: the LP stage of R(5,5) ≤ 46 ([Angeltveit–McKay](https://arxiv.org/abs/2409.15709)); Walker's LPs on subgraph-count identities gave R(4,5) ≤ 29, then ≤ 28, and McKay–Radziszowski extended them to ≤ 27 ([McKay–Radziszowski](https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf)); `linarith` finds such certificates ([Linarith](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html)).
- See also: T49, T54, T60, T61, T124, T128

### T49 Exact rational MIP certificates (VIPR)
`bound` `prove` · stage: certify · signals: inequality, integers
aka: exact SCIP, VIPR, vprchck, viprttn, MILP certificates, branch-and-bound tree certificate, Chvátal–Gomory cuts, ILP lower bounds
- What: a certificate lists the problem, solution, bounds and derivations (LP combinations, Chvátal–Gomory rounding, disjunctions); `vprchck` checks it and `viprttn` tightens it.
- Fits when: any ILP bound that has to count.
- Lean: every derivation is a rational linear combination plus rounding for CG cuts, so `linarith`/`linear_combination` can replay each node; a VIPR→Lean translator would be new.
- Example: the VIPR format and tools ([scipopt/vipr](https://github.com/scipopt/vipr)); its certificates were also re-checked with SMT ([Verifying MILP certificates with SMT](https://ar5iv.labs.arxiv.org/html/2312.10420)).
- See also: T13, T26, T48

### T50 Delsarte and Cohn–Elkies LP bounds
`bound` · stage: relax · signals: geometry, set-family, inequality
aka: Delsarte LP bound, association schemes, linear programming bound, sphere packing density, error-correcting codes, spherical designs, auxiliary function, dimensions 8 and 24
- What: an auxiliary function with sign conditions bounds code size or packing density.
- Fits when: upper bounds for codes, packings, spherical designs.
- Lean: a rational-coefficient auxiliary polynomial, its sign conditions proved by SOS (T54) or rational interval checks.
- Example: the best known sphere-packing bounds in dimensions 4–36, conjectured sharp in 8 and 24 ([Cohn–Elkies](https://arxiv.org/abs/math/0110009)).
- See also: T48, T53, T54

### T51 KKT conditions and Lagrangian duality
`bound` `prove` · stage: relax · signals: analytic, graph, inequality
aka: Karush–Kuhn–Tucker, Lagrange multipliers, Lagrangian dual, graph Lagrangian, hypergraph Lagrangian, Motzkin–Straus, Turán's theorem, local optimality
- What: first-order optimality conditions with multipliers for inequality-constrained problems; feasible multipliers certify local optimality, and the Lagrangian dual bounds the optimum.
- Fits when: a numerically found extremal configuration must be shown (locally) optimal, or a graph or hypergraph Lagrangian is maximized over a simplex.
- Lean: —
- Example: Motzkin–Straus (1965) proved Turán's theorem by maximizing the graph Lagrangian over the simplex ([Wikipedia: Turán's theorem](https://en.wikipedia.org/wiki/Tur%C3%A1n%27s_theorem); [Wikipedia: Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush%E2%80%93Kuhn%E2%80%93Tucker_conditions)).
- See also: T48, T98

### T52 First-order and arbitrary-precision conic solvers
`bound` · stage: relax · signals: inequality, matrix
aka: PDLP, primal-dual hybrid gradient, ADMM, SDPB, interior point, large LPs, large SDPs, high-precision SDP, bootstrap programs
- What: first-order methods (primal-dual hybrid gradient, ADMM) scale to LPs and SDPs that interior-point methods cannot hold in RAM; arbitrary-precision interior point gives the digits that exact rounding needs.
- Fits when: a Delsarte, flag-algebra or bootstrap program does not fit 32 GB, or rational rounding needs 50+ digits.
- Lean: — (they produce the numbers that exact rounding, T124, turns into certificates).
- Example: PDLP solves very large LPs with matrix-vector products only ([arXiv:2106.04756](https://arxiv.org/abs/2106.04756)); SDPB is a parallel arbitrary-precision SDP solver ([arXiv:1502.02033](https://arxiv.org/abs/1502.02033)).
- See also: T48, T53, T55, T124
