# Elementary combinatorial principles
Pigeonhole, averaging, double counting, extremal choices, invariants and monovariants, parity, descent, induction, bijections, involutions, inclusion–exclusion, LYM, chain decompositions and compression.

### T325 Pigeonhole principle
`prove` `find` · stage: argue · signals: integers, construction
aka: Dirichlet's box principle, drawer principle, generalized pigeonhole, coincidence, close pair, large fibre, Dirichlet's approximation theorem
- What: more objects than boxes forces a box with two; quantitatively, some box has at least the average.
- Fits when: you need existence of a coincidence, a close pair, or a large subset with a shared property.
- Lean: Mathlib: `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, `Fintype.exists_ne_map_eq_of_card_lt`, `Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to`; Dirichlet's theorem is `Real.exists_int_int_abs_mul_sub_le`.
- Example: Dirichlet's approximation theorem |qα - p| < 1/N with q ≤ N ([Wikipedia: Pigeonhole principle](https://en.wikipedia.org/wiki/Pigeonhole_principle), [Wikipedia: Dirichlet's approximation theorem](https://en.wikipedia.org/wiki/Dirichlet's_approximation_theorem)).
- See also: T326, T427, T620

### T326 Averaging
`prove` `find` `bound` · stage: argue · signals: random, construction
aka: max ≥ mean ≥ min, expectation argument, some element beats the average, random 2-colouring, diagonal Ramsey lower bound
- What: some element is at least the average, even when no explicit good element can be named.
- Fits when: an expectation or sum over all choices is computable.
- Lean: Mathlib: `Finset.exists_lt_of_sum_lt`; weighted forms such as `Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum` (`Combinatorics/Pigeonhole.lean`).
- Example: Erdős's random 2-colouring of K_n: the expected number of monochromatic K_k is below 1, so a good colouring exists ([Tricki: Averaging arguments](https://www.tricki.org/article/Averaging_arguments)).
- See also: T374, T325

### T327 Double counting
`prove` `bound` · stage: argue · signals: graph, set-family, inequality
aka: counting in two ways, incidence counting, flags, handshake lemma, Kővári–Sós–Turán, Zarankiewicz problem, K_{s,t}-free graphs, Erdős–Ko–Rado
- What: count one set (incidences, pairs, flags) in two ways and compare.
- Fits when: a quantity is a sum over a bipartite incidence structure.
- Lean: Mathlib: `Finset.card_mul_eq_card_mul` (`Combinatorics/Enumerative/DoubleCounting.lean`), `Finset.sum_comm`, `SimpleGraph.sum_degrees_eq_twice_card_edges`; Zarankiewicz numbers in `Combinatorics/SimpleGraph/Extremal/Zarankiewicz.lean`.
- Example: Katona-style double counting for the Erdős–Ko–Rado theorem; Kővári–Sós–Turán bound for K_{s,t}-free graphs ([Tricki: Double counting](https://www.tricki.org/article/Double_counting), [Wikipedia: Zarankiewicz problem](https://en.wikipedia.org/wiki/Zarankiewicz_problem)).
- See also: T369, T346, T443

### T328 Extremal principle
`prove` · stage: argue · signals: geometry, construction
aka: choose an extremal object, shortest, smallest, outermost, minimal distance pair, Sylvester–Gallai theorem, Kelly's proof
- What: pick an extremal object (shortest, smallest, outermost) and show a violation yields a more extreme one.
- Fits when: a configuration must contain a special element; finitely many candidates exist.
- Lean: Mathlib: `Set.exists_min_image` on a finite set, or `WellFounded.min`.
- Example: Kelly's proof of the Sylvester–Gallai theorem via the point-line pair of minimal distance ([Wikipedia: Sylvester–Gallai theorem](https://en.wikipedia.org/wiki/Sylvester–Gallai_theorem)).
- See also: T334, T333

### T329 Invariants
`prove` · stage: argue · signals: impossibility, parity
aka: preserved quantity, reachability, tiling obstruction, depleted grid, domino tilings, rectangles with an integer side, puzzles
- What: attach a quantity preserved by every allowed move; differing values prove impossibility.
- Fits when: "can state X be reached from Y?" or "can this region be tiled?"
- Lean: induction on the move sequence (`Relation.ReflTransGen`); finite boards by `decide +kernel`.
- Example: domino tilings of a depleted grid; rectangles tiled by rectangles with an integer side ([Tricki: Elementary examples of invariants](https://www.tricki.org/article/Elementary_examples_of_invariants)).
- See also: T330, T331, T332

### T330 Monovariants and potential functions
`prove` · stage: argue · signals: dynamics, impossibility
aka: monotone quantity, Lyapunov function, Lyapunov's direct method, energy function, entropy decrement, density increment, termination measure, ranking function, weights, Conway's soldiers, stability of equilibria, Erdős discrepancy problem, Perelman's entropy
- What: a quantity that strictly moves one way (and is bounded) proves termination or unreachability; decreasing along trajectories, it proves stability.
- Fits when: a process must stop, a target is "too far" in a weighted sense, an equilibrium of an ODE must be stable, or an iteration has no evident progress measure.
- Lean: termination by a measure (`termination_by`, `WellFounded`); Lyapunov certificates by SDP are T58.
- Example: Conway's soldiers: a golden-ratio weighting shows no soldier can reach row 5 ([Wikipedia: Conway's Soldiers](https://en.wikipedia.org/wiki/Conway's_Soldiers)); Lyapunov's direct method ([Wikipedia: Lyapunov function](https://en.wikipedia.org/wiki/Lyapunov_function)); Tao's Erdős discrepancy argument: each chunk either wins or drops entropy by a fixed amount ([Quanta](https://www.quantamagazine.org/a-magical-answer-to-an-80-year-old-puzzle-20151001/)); Perelman's entropy ([arXiv:math/0211159](https://arxiv.org/abs/math/0211159)).
- See also: T329, T58, T23, T686, T670

### T331 Colouring arguments
`prove` · stage: argue · signals: colouring, geometry, impossibility
aka: chessboard colouring, mutilated chessboard, de Bruijn's brick theorem, tiling obstructions, packing a box with bricks
- What: colour the board or space so every piece covers a fixed colour pattern; count colours.
- Fits when: tiling, packing or covering problems with local pieces.
- Lean: count each colour with `Finset.card_filter`-style sums; finite boards by `decide +kernel`.
- Example: mutilated chessboard; de Bruijn's theorem on packing a box with bricks ([Wikipedia: Mutilated chessboard problem](https://en.wikipedia.org/wiki/Mutilated_chessboard_problem), [Wikipedia: De Bruijn's theorem](https://en.wikipedia.org/wiki/De_Bruijn's_theorem)).
- See also: T329, T745

### T332 Parity counting
`prove` `find` · stage: argue · signals: parity, topology
aka: odd number of solutions, mod 2 count, handshake lemma, existence by parity, Sperner's lemma
- What: count something mod 2 to force existence (an odd number of solutions implies at least one).
- Fits when: objects pair up except for the ones you seek.
- Lean: Mathlib's handshake lemma `SimpleGraph.even_card_odd_degree_vertices`; parity steps by `omega` or in `ZMod 2`.
- Example: Sperner's lemma: the number of fully coloured simplices is odd ([Wikipedia: Sperner's lemma](https://en.wikipedia.org/wiki/Sperner's_lemma)).
- See also: T337, T708

### T333 Infinite descent
`prove` · stage: argue · signals: integers, impossibility
aka: Fermat's descent, well-ordering, minimal solution, x⁴ + y⁴ = z², Diophantine nonexistence
- What: from a solution build a strictly smaller one in a well-ordered set.
- Fits when: Diophantine nonexistence, or a minimal object can be shrunk.
- Lean: Mathlib: `not_fermat_42` (`NumberTheory/FLT/Four.lean`) is Fermat's x⁴ + y⁴ = z²; descent by `Nat.strong_induction_on` or `WellFounded.induction`.
- Example: Fermat's proof of no nontrivial solutions to x^4 + y^4 = z^2 ([Wikipedia: Proof by infinite descent](https://en.wikipedia.org/wiki/Proof_by_infinite_descent)).
- See also: T334, T515

### T334 Minimal counterexample
`prove` · stage: argue · signals: graph, colouring, induction-stuck
aka: minimal criminal, smallest counterexample, reducible configurations, critical graphs, four colour theorem
- What: study a smallest counterexample and show it has impossible structure.
- Fits when: the property is hereditary or reducible configurations can be removed.
- Lean: take the counterexample with `Nat.find` or `WellFounded.min`, then derive `False`.
- Example: the four colour theorem: a minimal counterexample contains none of an unavoidable set of reducible configurations ([Wikipedia: Four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem)).
- See also: T464, T302, T333

### T335 Induction variants
`prove` · stage: argue · signals: induction-stuck
aka: strong induction, structural induction, transfinite induction, Cauchy's forward-backward induction, induction on 2^k, AM–GM
- What: strong, structural, transfinite, or Cauchy's forward-backward induction (prove for 2^k, then step down).
- Fits when: the natural ordering is not n → n+1.
- Lean: `Nat.strong_induction_on`, `Nat.le_induction`, `Nat.decreasingInduction`; `induction` on any inductive type.
- Example: Cauchy's forward-backward proof of AM–GM ([Wikipedia: Inequality of arithmetic and geometric means](https://en.wikipedia.org/wiki/Inequality_of_arithmetic_and_geometric_means), [Wikipedia: Mathematical induction](https://en.wikipedia.org/wiki/Mathematical_induction)).
- See also: T302, T767

### T336 Bijective proof
`prove` `compute` · stage: argue · signals: exact-value, identity
aka: combinatorial bijection, equinumerous sets, Prüfer codes, Cayley's formula n^(n-2), labelled trees, Catalan numbers
- What: show two sets are equinumerous by an explicit bijection.
- Fits when: a count is suspiciously clean (n^(n-2), Catalan numbers).
- Lean: Mathlib: `Finset.card_bij`, `Fintype.card_congr`; small instances by `decide +kernel`.
- Example: Prüfer codes give Cayley's formula n^(n-2) for labelled trees ([Wikipedia: Bijective proof](https://en.wikipedia.org/wiki/Bijective_proof), [Wikipedia: Cayley's formula](https://en.wikipedia.org/wiki/Cayley's_formula)).
- See also: T337, T456, T447

### T337 Involution with few fixed points
`prove` · stage: argue · signals: parity, integers
aka: sign-reversing involution, fixed-point parity, Zagier's one-sentence proof, Fermat's two-squares theorem, primes p ≡ 1 mod 4
- What: an involution on a finite set has fixed points of the same parity as the set; a second involution transfers the count.
- Fits when: existence of a special element is to be shown via parity of fixed points.
- Lean: Mathlib's Archive formalizes Zagier's proof (`Archive/ZagierTwoSquares.lean`); Mathlib: `Nat.Prime.sq_add_sq`.
- Example: Zagier's one-sentence proof that every prime p ≡ 1 mod 4 is a sum of two squares ([Wikipedia: Fermat's theorem on sums of two squares](https://en.wikipedia.org/wiki/Fermat's_theorem_on_sums_of_two_squares)).
- See also: T332, T336

### T338 Inclusion–exclusion
`compute` `prove` · stage: argue · signals: exact-value, set-family
aka: principle of inclusion–exclusion, sieve formula, zeta transform, inclusion–exclusion with the zeta transform, Bonferroni, derangements, counting complements
- What: count the union or the complement by alternating sums over intersections.
- Fits when: "none of the bad properties" with computable intersections.
- Lean: Mathlib: `Finset.inclusion_exclusion_card_biUnion`, `Finset.inclusion_exclusion_card_inf_compl`; derangements `card_derangements_eq_numDerangements`, `numDerangements_sum`.
- Example: the derangement count n!Σ(-1)^k/k! ([Wikipedia: Inclusion–exclusion principle](https://en.wikipedia.org/wiki/Inclusion–exclusion_principle), [Wikipedia: Derangement](https://en.wikipedia.org/wiki/Derangement)).
- See also: T454, T505, T1113

### T339 Coefficient extraction
`compute` `prove` · stage: argue · signals: polynomial, exact-value, congruence
aka: roots-of-unity filter, series multisection, residues, orthogonality, kill the other terms, binomial sums over residue classes
- What: isolate one term by an operation that kills all others (averaging over roots of unity, residues, orthogonality).
- Fits when: you need every k-th coefficient or one Fourier mode.
- Lean: Mathlib: `IsPrimitiveRoot.geom_sum_eq_zero`.
- Example: sums of binomial coefficients over residue classes ([Tricki: kill all the other terms](https://www.tricki.org/article/To_find_the_value_of_a_coefficient_do_something_that_kills_all_the_other_terms)).
- See also: T479, T447

### T340 Telescoping
`compute` `prove` · stage: argue · signals: sequence, identity, exact-value
aka: antidifferencing, discrete antiderivative, partial fractions, collapsing sums
- What: write terms as differences of a sequence so the sum collapses.
- Fits when: an exact sum is wanted and partial fractions or discrete antiderivatives exist.
- Lean: Mathlib: `Finset.sum_range_sub`; WZ certificates are T61.
- Example: Σ 1/(n(n+1)) = 1 and its relatives ([Tricki: antidifferencing](https://www.tricki.org/article/To_calculate_an_infinite_sum_exactly_try_antidifferencing)).
- See also: T61, T648

### T341 Greedy construction and exchange argument
`find` `bound` · stage: construct · signals: graph, colouring, construction
aka: greedy algorithm, exchange argument, matroids, greedy colouring with Δ + 1 colours, first fit
- What: build step by step taking the locally best choice; show an optimal solution can be exchanged into the greedy one.
- Fits when: matroid-like structure, or only a bound (not optimum) is needed.
- Lean: define the greedy object by recursion, prove its invariant by induction; a concrete output by `decide +kernel`.
- Example: greedy colouring uses at most Δ + 1 colours ([Tricki: Greedy algorithms](https://www.tricki.org/article/Greedy_algorithms)).
- See also: T342, T811

### T342 Just-do-it construction
`find` · stage: construct · signals: construction
aka: step-by-step construction, inductive construction, countably many requirements, dense sets with extra properties
- What: build the object one element at a time; at each step only finitely many constraints block you.
- Fits when: countably many requirements, each excludable by a small set.
- Lean: define the sequence by recursion and prove requirement n is met at stage n.
- Example: constructing dense sets with extra properties and exponentially large families ([Tricki: Just-do-it proofs](https://www.tricki.org/article/Just-do-it_proofs)).
- See also: T341, T343, T767

### T343 Diagonal argument
`prove` · stage: argue · signals: logic, computation, impossibility
aka: diagonalization, Cantor's theorem, uncountability of the reals, escaping a countable list, halting problem, time hierarchy theorem
- What: build an object differing from the n-th listed object at the n-th place.
- Fits when: showing something escapes every member of a countable list.
- Lean: Mathlib: `Function.cantor_surjective`, `Cardinal.not_countable_real`.
- Example: Cantor's uncountability of the reals ([Tricki: Diagonal arguments](https://www.tricki.org/article/Diagonal_arguments)); the time hierarchy theorem ([Wikipedia: Time hierarchy theorem](https://en.wikipedia.org/wiki/Time_hierarchy_theorem)).
- See also: T768, T771

### T344 Counting by orbits or classes
`compute` `prove` · stage: argue · signals: group, congruence, symmetric
aka: partition into equal classes, free group action, uniform fibration, orbit–stabilizer, divisibility from orbit sizes, Σ_{d|n} φ(d) = n
- What: split a set into equal-size classes to read off divisibility or size.
- Fits when: a set has a free group action or a uniform fibration.
- Lean: Mathlib: `MulAction.card_eq_sum_card_group_div_card_stabilizer`, `Nat.sum_totient`.
- Example: binomial coefficients by partitioning strings; the identity Σ_{d|n} φ(d) = n by partitioning {1..n} by gcd ([Tricki: Counting by partitioning](https://www.tricki.org/article/Counting_by_partitioning)).
- See also: T455, T315, T38

### T345 Same object, two patterns
`prove` · stage: argue · signals: symmetric, identity
aka: symmetry for free, mirror image, relabelling, apply a lemma twice, pons asinorum
- What: substitute one object into a pattern in two ways to get an identity or symmetry for free.
- Fits when: a statement looks symmetric in hidden roles.
- Lean: apply the lemma twice with permuted arguments; `wlog` for symmetric cases.
- Example: equal base angles imply equal sides, by matching triangle ABC with its mirror image ACB ([Tricki: same object fits a pattern two ways](https://www.tricki.org/article/Recognize_that_the_same_object_fits_a_pattern_in_two_different_ways)).
- See also: T315

### T346 Turn sets into functions
`prove` `bound` · stage: reformulate · signals: additive, set-family
aka: indicator functions, characteristic functions, counting by sums, convolution, Fourier analysis of sets, counting progressions
- What: replace sets by indicator functions so sums, convolutions and Fourier analysis apply.
- Fits when: counting configurations inside sets.
- Lean: Mathlib: `Set.indicator`; convolutions of finite sets in `Combinatorics/Additive/Convolution.lean`.
- Example: counting arithmetic progressions in A as Σ 1_A(x)1_A(x+d)1_A(x+2d) ([Tricki: Turn sets into functions](https://www.tricki.org/article/Turn_sets_into_functions)).
- See also: T412, T327

### T347 Weighting (LYM)
`prove` `bound` · stage: argue · signals: set-family, order, inequality
aka: LYM inequality, Lubell–Yamamoto–Meshalkin, Sperner's theorem, antichains in the Boolean lattice, random maximal chain
- What: give each object a weight so a random chain meets the family at most once on average.
- Fits when: antichain or intersecting-family bounds.
- Lean: Mathlib: `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, `IsAntichain.sperner` (`Combinatorics/SetFamily/LYM.lean`).
- Example: Lubell's proof of Sperner's theorem via the LYM inequality ([Wikipedia: LYM inequality](https://en.wikipedia.org/wiki/Lubell–Yamamoto–Meshalkin_inequality)).
- See also: T348, T369, T349

### T348 Chain and antichain decompositions
`prove` · stage: argue · signals: order, sequence
aka: Dilworth's theorem, Mirsky's theorem, chain covers, antichain partitions, posets, divisibility posets, Erdős–Szekeres theorem, monotone subsequences
- What: the largest antichain equals the fewest chains covering a poset; dually the longest chain equals the fewest antichains.
- Fits when: a poset hides in the problem (sequences, divisibility, set families).
- Lean: Erdős–Szekeres is in Mathlib's Archive (`erdos_szekeres` in `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`); a grep finds no Dilworth or Mirsky theorem in Mathlib.
- Example: Erdős–Szekeres on monotone subsequences as an application of Dilworth ([Wikipedia: Dilworth's theorem](https://en.wikipedia.org/wiki/Dilworth%27s_theorem)).
- See also: T347, T325

### T349 Compression
`prove` `bound` · stage: argue · signals: set-family, order, inequality
aka: shifting, UV-compression, down-compression, shadows, colex initial segments, Kruskal–Katona theorem, Erdős–Ko–Rado theorem
- What: repeatedly replace elements by "smaller" ones, preserving the constraint, until the family is canonical.
- Fits when: extremal set-family problems whose extremizers look like initial segments.
- Lean: Mathlib: `Combinatorics/SetFamily/Compression/UV.lean`; `kruskal_katona` and `erdos_ko_rado` in `Combinatorics/SetFamily/KruskalKatona.lean`.
- Example: Kruskal–Katona shadow theorem; shifting proofs of Erdős–Ko–Rado ([Wikipedia: Kruskal–Katona theorem](https://en.wikipedia.org/wiki/Kruskal–Katona_theorem), [Wikipedia: Erdős–Ko–Rado theorem](https://en.wikipedia.org/wiki/Erdős–Ko–Rado_theorem)).
- See also: T369, T347, T371
