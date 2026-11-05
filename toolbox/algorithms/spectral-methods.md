# Spectral methods and expanders
Lovász theta, expander constructions, spectral sparsifiers, planted-structure recovery and high-dimensional expanders.

### T1071 Lovász theta
`bound` · stage: relax · signals: graph, matrix, inequality
aka: Lovász number, ϑ(G), semidefinite relaxation, SDP bound, orthonormal representation, Shannon capacity, C₅, independence number, clique number, sandwich theorem
- What: ϑ(G), computable by SDP, lies between α(G) and χ̄(G); an orthonormal representation or dual SDP solution certifies the bound.
- Fits when: bounds on independence or clique numbers and on Shannon capacity, especially with symmetry.
- Lean: round the dual SDP solution to rationals (T124) and check it as in T53.
- Example: Lovász's proof that the Shannon capacity of C₅ is √5 ([Wikipedia: Lovász number](https://en.wikipedia.org/wiki/Lov%C3%A1sz_number)).
- See also: T53, T57, T1017, T1004

### T1072 Zig-zag and graph products
`find` · stage: construct · signals: graph, product-structure, construction
aka: zig-zag product, graph products, constant-degree expanders, Reingold–Vadhan–Wigderson, recursive constructions, explicit expanders of all sizes
- What: combines a big graph and a small graph while keeping expansion.
- Fits when: explicit constant-degree constructions; recursive constructions in general.
- Lean: —
- Example: constant-degree expanders of all sizes ([Reingold–Vadhan–Wigderson](https://arxiv.org/abs/math/0406038)).
- See also: T1067, T1075

### T1073 Barrier-potential method (BSS)
`find` · stage: construct · signals: graph, matrix, sparse
aka: Batson–Spielman–Srivastava, spectral sparsifiers, twice-Ramanujan sparsifiers, rank-one updates, upper and lower potentials, deterministic spectral constructions
- What: adds rank-one terms one at a time while upper and lower potentials keep every eigenvalue in a window.
- Fits when: deterministic constructions with spectral guarantees; sparsifying certificates.
- Lean: —
- Example: twice-Ramanujan sparsifiers with ⌈d(n−1)⌉ edges ([Batson–Spielman–Srivastava](https://arxiv.org/abs/0808.0163)).
- See also: T1072

### T1074 Spectral recovery of planted structure
`find` · stage: explore · signals: graph, matrix, random
aka: planted clique, hidden partition, top eigenvectors, Alon–Krivelevich–Sudakov, spectral detection, near-extremal colourings, structure in experimental data
- What: top eigenvectors reveal a hidden clique or partition.
- Fits when: detecting hidden structure in experimental data, such as near-extremal colourings.
- Lean: — (the recovered structure is a hypothesis)
- Example: Alon–Krivelevich–Sudakov find planted cliques of size about 10√n and larger ([Wikipedia: Planted clique](https://en.wikipedia.org/wiki/Planted_clique)).
- See also: T1056, T1017

### T1075 High-dimensional expanders
`bound` `compute` · stage: argue · signals: matrix, random, topology
aka: local-to-global, simplicial complexes, spectral gaps of links, high-order random walks, matroid bases, Mihail–Vazirani conjecture, counting and sampling bases
- What: spectral gaps of the links of a simplicial complex imply mixing of high-order random walks.
- Fits when: sampling or counting on matroid bases and other complexes; code constructions.
- Lean: —
- Example: Anari–Liu–Oveis Gharan–Vinzant prove the Mihail–Vazirani conjecture and count matroid bases ([arXiv:1811.01816](https://arxiv.org/abs/1811.01816)).
- See also: T1052, T1123, T1081
