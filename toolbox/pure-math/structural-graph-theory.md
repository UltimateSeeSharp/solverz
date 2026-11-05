# Structural graph theory
Colouring and structure arguments for graphs: discharging, recolouring, orientations, minors and decompositions, min–max duality, and explicit lifts of small graphs.

### T464 Discharging with unavoidable reducible configurations
`prove` · stage: argue · signals: graph, colouring, sparse, impossibility
aka: discharging method, unavoidable set plus reducibility, reducible configurations, charges via Euler's formula, minimal counterexample, four colour theorem, planar and bounded-genus graphs, proof by reflection
- What: assign charges with a negative total (Euler's formula), move charge by local rules, and show some configuration from an explicit finite list must occur; each listed configuration is reducible.
- Fits when: colouring or structural statements for planar or bounded-genus graphs; minimal-counterexample proofs.
- Lean: a Lean checker for the unavoidable set and the reducibility tests, with a soundness proof, run by `decide +kernel` (T120); each configuration is a separate theorem (T122).
- Example: the four colour theorem (Appel–Haken; Robertson–Sanders–Seymour–Thomas), formally verified in Coq by Gonthier ([Wikipedia: Discharging method](https://en.wikipedia.org/wiki/Discharging_method_%28discrete_mathematics%29), [Wikipedia: Four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem), [Gonthier](https://www.cl.cam.ac.uk/~lp15/Pages/4colproof.pdf)).
- See also: T334, T465, T120, T122

### T465 Kempe chains and alternating paths
`prove` · stage: argue · signals: graph, colouring
aka: Kempe swap, two-coloured components, recolouring, fans, Vizing's theorem, five colour theorem, edge colouring
- What: swaps the two colours along a two-coloured component to free a colour.
- Fits when: recolouring arguments in vertex or edge colouring.
- Lean: Mathlib `SimpleGraph.Coloring`; the swap argument by hand.
- Example: the five colour theorem; Vizing's theorem via fans and alternating paths ([Wikipedia: Five color theorem](https://en.wikipedia.org/wiki/Five_color_theorem), [Wikipedia: Vizing's theorem](https://en.wikipedia.org/wiki/Vizing's_theorem)).
- See also: T464, T475

### T466 Kernels in orientations
`prove` · stage: argue · signals: graph, colouring
aka: kernel-perfect orientations, Galvin's theorem, Dinitz conjecture, list edge-colouring, stable matchings, Latin squares
- What: an orientation in which every induced subgraph has a kernel yields list colourings.
- Fits when: list edge-colouring of bipartite-type graphs.
- Lean: —
- Example: Galvin's proof of the Dinitz conjecture ([Wikipedia: List edge-coloring](https://en.wikipedia.org/wiki/List_edge-coloring)).
- See also: T467

### T467 Alon–Tarsi orientations
`prove` · stage: argue · signals: graph, colouring, polynomial
aka: graph polynomial, Eulerian subgraphs even vs odd, choosability, list colouring, planar bipartite graphs 3-choosable
- What: a nonvanishing coefficient of the graph polynomial (even vs odd Eulerian subgraphs) gives choosability.
- Fits when: choosability of bipartite or planar graphs.
- Lean: one coefficient or one Eulerian-subgraph count by `decide +kernel` for a fixed graph.
- Example: planar bipartite graphs are 3-choosable ([Alon: Combinatorial Nullstellensatz](https://www.tau.ac.il/~nogaa/PDFS/null2.pdf)).
- See also: T391, T466

### T468 Graph minors structure theory
`prove` · stage: argue · signals: graph, order
aka: Robertson–Seymour theorem, excluded minors, tree decompositions, near-embeddable pieces, well-quasi-ordering, finite obstruction sets, treewidth
- What: excluded-minor classes decompose into near-embeddable pieces along trees; minors are well-quasi-ordered.
- Fits when: properties closed under minors; algorithmic finiteness.
- Lean: —
- Example: Robertson–Seymour theorem: every minor-closed class has a finite obstruction set ([Wikipedia: Robertson–Seymour theorem](https://en.wikipedia.org/wiki/Robertson–Seymour_theorem)).
- See also: T766, T472

### T469 Decomposition theorems
`prove` · stage: argue · signals: graph, classification
aka: basic classes, 2-joins, skew partitions, hereditary classes, forbidden induced subgraphs, strong perfect graph theorem, Berge graphs
- What: every graph in a class is basic or has a decomposition (2-join, skew partition) that preserves the property.
- Fits when: hereditary classes defined by forbidden induced subgraphs.
- Lean: —
- Example: the strong perfect graph theorem ([Wikipedia: Strong perfect graph theorem](https://en.wikipedia.org/wiki/Strong_perfect_graph_theorem)).
- See also: T468, T334

### T470 Min–max duality
`prove` `compute` · stage: argue · signals: graph, exact-value
aka: Menger's theorem, max-flow min-cut, König's theorem, total unimodularity, LP duality, disjoint paths, vertex covers, packing equals cover
- What: maximum packing equals minimum cover, by LP duality or augmenting paths.
- Fits when: connectivity, matching, disjoint paths; certificates on both sides.
- Lean: for a fixed graph, both certificates (a packing and a cover of equal size) checked by `decide +kernel`.
- Example: Menger's theorem and König's theorem via total unimodularity ([Wikipedia: Max-flow min-cut theorem](https://en.wikipedia.org/wiki/Max-flow_min-cut_theorem), [Wikipedia: Unimodular matrix](https://en.wikipedia.org/wiki/Unimodular_matrix)).
- See also: T471, T48, T316

### T471 Hall-type conditions and alternating paths
`prove` `find` · stage: argue · signals: graph, set-family
aka: Hall's marriage theorem, systems of distinct representatives, Tutte's theorem, Berge's lemma, augmenting paths, perfect matchings, Tutte violators
- What: a matching exists iff no set has too few neighbours; Tutte and Berge generalize.
- Fits when: perfect matchings, systems of distinct representatives.
- Lean: Mathlib `Finset.all_card_le_biUnion_card_iff_exists_injective` (Hall) and `SimpleGraph.tutte`.
- Example: Hall's marriage theorem; Tutte's theorem; Berge's augmenting-path lemma ([Wikipedia: Hall's marriage theorem](https://en.wikipedia.org/wiki/Hall's_marriage_theorem), [Wikipedia: Tutte's theorem on perfect matchings](https://en.wikipedia.org/wiki/Tutte's_theorem_on_perfect_matchings), [Wikipedia: Berge's theorem](https://en.wikipedia.org/wiki/Berge's_theorem)).
- See also: T470, T465

### T472 Degeneracy and density bounds for minors
`bound` · stage: argue · signals: graph, colouring, asymptotic
aka: Hadwiger's conjecture, K_t minors, average degree, degeneracy, greedy colouring, Kostochka–Thomason, Delcourt–Postle
- What: bounds the average degree of graphs without a K_t minor, so greedy colouring applies.
- Fits when: Hadwiger-type colouring bounds.
- Lean: —
- Example: Kostochka–Thomason O(t√log t); Delcourt–Postle O(t log log t) ([Wikipedia: Hadwiger conjecture](https://en.wikipedia.org/wiki/Hadwiger_conjecture_%28graph_theory%29), [arXiv:2108.01633](https://arxiv.org/abs/2108.01633)).
- See also: T468

### T473 Separators from geometry
`prove` `bound` · stage: argue · signals: graph, geometry, sparse
aka: planar separator theorem, Lipton–Tarjan, circle packing, Koebe–Andreev–Thurston, balanced separators, minor-free graphs, divide and conquer
- What: circle packings or geometric embeddings give balanced small separators.
- Fits when: planar or minor-free graphs; divide-and-conquer algorithms.
- Lean: —
- Example: the planar separator theorem via Koebe–Andreev–Thurston circle packing ([Wikipedia: Planar separator theorem](https://en.wikipedia.org/wiki/Planar_separator_theorem)).
- See also: T743

### T474 Deletion–contraction
`compute` `prove` · stage: argue · signals: graph, polynomial, exact-value
aka: Tutte polynomial, chromatic polynomial, flow polynomial, spanning trees, G − e and G/e recursion, universality
- What: expresses an invariant recursively on G − e and G/e; universal invariants (Tutte polynomial) follow.
- Fits when: graph polynomials, counting colourings, flows, spanning trees.
- Lean: values for a fixed small graph by `decide +kernel`.
- Example: Tutte polynomial universality ([Wikipedia: Tutte polynomial](https://en.wikipedia.org/wiki/Tutte_polynomial)).
- See also: T408, T460

### T475 Brooks-type local arguments
`prove` `bound` · stage: argue · signals: graph, colouring, inequality
aka: Brooks' theorem, χ ≤ Δ, good vertex orderings, non-adjacent neighbours, saving one colour, degree-choosability
- What: chooses a good vertex ordering or local structure (non-adjacent neighbours) to save one colour.
- Fits when: colouring bounds near the maximum degree.
- Lean: Mathlib `SimpleGraph.chromaticNumber`; the ordering argument by hand.
- Example: Brooks' theorem χ ≤ Δ unless complete or an odd cycle ([Wikipedia: Brooks' theorem](https://en.wikipedia.org/wiki/Brooks'_theorem)).
- See also: T465

### T476 Voltage-graph lifts and excision
`find` `bound` · stage: construct · signals: graph, symmetric, construction
aka: cages, (k,g)-graphs, record graphs rec(k,g), derived graph, regular covers, graph covers, voltage assignments, small regular graphs of given girth, Moore bound, Petersen and Heawood graphs as lifts
- What: a lift assigns group elements (voltages) to the arcs of a small base graph and takes V(G)×Γ as vertices; excision deletes a subgraph with degrees {1, k} from a (k,g)-graph and re-pairs the loose ends, aiming at girth ≥ g − 1.
- Fits when: small regular graphs of given girth (cage upper bounds); search over voltages on a small base graph instead of over graphs.
- Lean: the graph is an explicit finite witness; regularity and the absence of short cycles by a kernel-run checker (T118, T120); Mathlib has `SimpleGraph.girth`.
- Example: rec(3,16) = 960 is a lift of the Petersen graph with voltages in Z2 × Z48; Balaban's (3,11)-cage came by excision from the (3,12)-cage ([Exoo–Jajcay, Dynamic Cage Survey](https://www.combinatorics.org/files/Surveys/ds16/ds16v3-2013.pdf)); exhaustive lifts, tabu search, hill climbing and excision gave new bounds in eleven cases, including n(4,10) ≤ 320 ([arXiv:2511.07247](https://arxiv.org/abs/2511.07247)).
- See also: T366, T401, T27, T90

### T840 Exponential graphs
`find` `prove` · stage: construct · signals: graph, colouring, construction
aka: exponential graph, K^G, E_c(G), categorical product, tensor product of graphs, graph homomorphisms, multiplicative graphs, Hedetniemi's conjecture, Shitov, El-Zahar–Sauer, colourings of products
- What: K^G has all maps V(G) → V(K) as vertices, f adjacent to g when f(v) is adjacent to g(v') for every edge vv' of G; homomorphisms G × H → K correspond to homomorphisms H → K^G, so G × K^G is the hardest instance of a product-colouring question.
- Fits when: a claim about colourings or homomorphisms of products, such as χ(G × H) = min(χ(G), χ(H)); reduce to H = K^G and bound the chromatic number of the exponential graph.
- Lean: Mathlib's colourings are homomorphisms (`SimpleGraph.Coloring α` is `G →g completeGraph α`); the categorical product is not there (only `boxProd`), so define it by adjacency in both coordinates; a given finite colouring is a witness (T118).
- Example: Shitov's counterexample: with c = ⌈3.1q⌉, q large, and G of girth at least 6 and fractional chromatic number above 3.1, the product (G ⊠ K_q) × E_c(G ⊠ K_q) breaks Hedetniemi's conjecture ([arXiv:1905.02167](https://arxiv.org/abs/1905.02167); zbMATH review via [MaRDI](https://portal.mardi4nfdi.de/wiki/Item:Q2274002)); El-Zahar–Sauer's 4-chromatic case is a homomorphism out of an exponential graph ([Tardif, Fields talk](https://fieldsinstitute.ca/talks/Duality-and-exponential-graphs), [Wikipedia: Hedetniemi's conjecture](https://en.wikipedia.org/wiki/Hedetniemi%27s_conjecture)); the conjecture now fails for all n ≥ 4 and holds for n ≤ 3 ([Zhu's survey, arXiv:2502.16078](https://arxiv.org/abs/2502.16078)).
- See also: T1370, T465, T118
