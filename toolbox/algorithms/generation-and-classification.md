# Generation and classification
Enumeration methods beyond canonical augmentation (T30): homomorphism chains, reverse search, refinement filters, specialized generators, code and design classification.

### T1088 Method of homomorphisms (Laue)
`compute` · stage: generate · signals: group, set-family, classification
aka: Laue's method, homomorphism principle, chains of quotients, sub-structures, degree partitions, designs, group computations between levels
- What: generates along combinatorially defined sub-objects, with group computations between levels.
- Fits when: objects with a natural chain of quotients or sub-structures (degree partitions, designs).
- Lean: as for T30: prove a cover lemma, then check each case.
- Example: described alongside canonical augmentation ([McKay 1998](https://users.cecs.anu.edu.au/~bdm/papers/orderly.pdf)).
- See also: T29, T30

### T1089 Reverse search
`compute` · stage: generate · signals: geometry, graph, classification
aka: Avis–Fukuda, parent function, spanning tree of objects, depth-first enumeration without a visited set, polynomial memory, vertices of polytopes, triangulations, spanning trees, local moves
- What: defines a parent function on objects and walks the resulting spanning tree depth-first; polynomial memory and no visited set.
- Fits when: enumeration where objects are connected by local moves and symmetry is weak; trivially parallel.
- Lean: completeness rests on the parent function reaching the root from every object; prove that once, then check the list.
- Example: vertices of polytopes, triangulations, spanning trees ([Wikipedia: Reverse-search algorithm](https://en.wikipedia.org/wiki/Reverse-search_algorithm)).
- See also: T1083, T1104

### T1090 Colour refinement (1-WL)
`compute` · stage: generate · signals: graph, symmetric
aka: Weisfeiler–Leman, 1-dimensional WL, vertex colour refinement, graph invariants, hashing into buckets, pre-filtering before canonical labelling, isomorphism testing
- What: cheap iterated vertex colourings that separate most non-isomorphic graphs.
- Fits when: fast pre-filtering before canonical labelling; hashing into buckets.
- Lean: a difference in the refined colour counts proves non-isomorphism and can be checked by `decide`; equal colourings prove nothing.
- Example: [Wikipedia: Weisfeiler–Leman graph isomorphism test](https://en.wikipedia.org/wiki/Weisfeiler_Leman_graph_isomorphism_test).
- See also: T30, T1093

### T1091 Specialized generators
`compute` · stage: generate · signals: graph, classification
aka: GENREG, plantri, regular graphs, cubic graphs, planar graphs, snarks, cages, (5,5)-cages, tuned generators, reuse before writing your own
- What: generators tuned to a class (cubic, regular, planar, snarks) beat generic ones by orders of magnitude.
- Fits when: before writing your own generator.
- Lean: as for T30: prove a cover lemma, then check each case.
- Example: all snarks up to 36 vertices ([Brinkmann–Goedgebeur–Hägglund–Markström](https://arxiv.org/abs/1206.6690)); GENREG listed all 5-regular graphs on 16 vertices and found exactly four (5,5)-cages ([Meringer](https://www.mathe2.uni-bayreuth.de/markus/pdf/pub/FastGenRegGraphJGT.pdf)); plantri generates planar graphs at more than 5M per second ([plantri](https://users.cecs.anu.edu.au/~bdm/plantri/)).
- See also: T30, T81

### T1092 Classification of codes and designs
`compute` · stage: generate · signals: set-family, symmetric, classification
aka: Kaski–Östergård, classification algorithms, isomorph rejection, prescribed groups, catalogue checking, error-correcting codes, block designs, BIBDs, Latin squares
- What: combines isomorph rejection, prescribed groups and catalogue checks for codes and designs.
- Fits when: compute problems on designs, codes and Latin squares.
- Lean: as for T30: prove a cover lemma, then check each case.
- Example: [Kaski–Östergård, Classification Algorithms for Codes and Designs](https://users.aalto.fi/~pat/cacd.html).
- See also: T27, T30, T1087

### T1093 Graph isomorphism in quasipolynomial time
`compute` · stage: judge · signals: graph, symmetric
aka: Babai, graph isomorphism problem, GI, quasipolynomial time, canonical forms are rarely the bottleneck, where enumeration time goes
- What: graph isomorphism is quasipolynomial, so canonical forms are rarely the true bottleneck.
- Fits when: judging where the time of an enumeration goes.
- Lean: —
- Example: [Babai](https://arxiv.org/abs/1512.03547).
- See also: T30, T1090
