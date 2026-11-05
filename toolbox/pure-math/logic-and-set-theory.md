# Logic, model theory and set theory
Compactness and finite-to-infinite transfer, model-theoretic tools, independence, ordinals and well-quasi-orders, undecidability, definable combinatorics.

### T751 Compactness theorem
`prove` · stage: reformulate · signals: logic, colouring, graph
aka: compactness to finite, finite satisfiability, De Bruijn–Erdős, Rado selection principle, infinite colourings, infinite tilings, sequences avoiding patterns, every finite subgraph
- What: a theory is consistent iff every finite part is; an infinite statement becomes "every finite piece", and a finite piece is then exhibited or refuted.
- Fits when: an infinite structure property is determined by finite substructures (colourings, orderings, tilings).
- Lean: Mathlib: `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`; combinatorial form `Finset.rado_selection`; a refuting finite piece by `decide +kernel` or SAT (T5).
- Example: De Bruijn–Erdős: an infinite graph is k-colourable iff every finite subgraph is ([Wikipedia: Compactness theorem](https://en.wikipedia.org/wiki/Compactness_theorem), [Wikipedia: De Bruijn–Erdős theorem](https://en.wikipedia.org/wiki/De_Bruijn–Erdős_theorem_%28graph_theory%29)).
- See also: T752, T313, T5

### T752 König's lemma
`prove` · stage: argue · signals: logic, order
aka: Kőnig's infinity lemma, finitely branching trees, infinite paths, finite-to-infinite, arbitrarily large finite objects
- What: an infinite finitely branching tree has an infinite path.
- Fits when: passing from "arbitrarily large finite" to "infinite" combinatorial objects, or back.
- Lean: Mathlib: `exists_seq_forall_proj_of_forall_finite`, `exists_orderEmbedding_covby_of_forall_covby_finite` (Order/KonigLemma.lean).
- Example: finite-to-infinite colouring and tiling arguments ([Wikipedia: Kőnig's lemma](https://en.wikipedia.org/wiki/Kőnig's_lemma)).
- See also: T751

### T753 Ultraproducts and Łoś's theorem
`prove` · stage: reformulate · signals: logic, finite-field
aka: Łoś's theorem, ultrapowers, Ax–Kochen, transfer between characteristics, almost all primes, limits of finite structures
- What: a first-order statement holds in an ultraproduct iff it holds in almost all factors.
- Fits when: transferring between families of finite structures and one infinite limit.
- Lean: Mathlib: `FirstOrder.Language.Ultraproduct.sentence_realize`.
- Example: Ax–Kochen: for each d, almost all p satisfy Artin's conjecture on p-adic forms ([Wikipedia: Ultraproduct](https://en.wikipedia.org/wiki/Ultraproduct), [Wikipedia: Ax–Kochen theorem](https://en.wikipedia.org/wiki/Ax–Kochen_theorem), [Wikipedia: Łoś's theorem](https://en.wikipedia.org/wiki/Łoś's_theorem)).
- See also: T754, T774, T586

### T754 Nonstandard analysis
`prove` · stage: reformulate · signals: logic, analytic
aka: infinitesimals, hyperreals, hyperfinite objects, transfer principle, Robinson, internal sets
- What: reasons with infinitesimals and hyperfinite objects, then transfers back.
- Fits when: compactness-heavy analysis, limits of finite structures.
- Lean: Mathlib defines `Hyperreal` as an ultrapower of ℝ.
- Example: Bernstein–Robinson invariant subspace result for polynomially compact operators ([Wikipedia: Nonstandard analysis](https://en.wikipedia.org/wiki/Nonstandard_analysis)).
- See also: T753, T313

### T755 Löwenheim–Skolem
`prove` · stage: argue · signals: logic
aka: downward Löwenheim–Skolem, upward Löwenheim–Skolem, countable elementary submodels, Skolem hulls, models of a given cardinality
- What: a theory with an infinite model has models of every infinite cardinality.
- Fits when: reducing to countable structures, building models of given size.
- Lean: Mathlib: `FirstOrder.Language.exists_elementarySubstructure_card_eq`.
- Example: countable elementary submodels in set theory ([Wikipedia: Löwenheim–Skolem theorem](https://en.wikipedia.org/wiki/Löwenheim–Skolem_theorem)).
- See also: T751, T759

### T756 o-minimality and point counting
`prove` `bound` · stage: argue · signals: logic, arithmetic-geometry, asymptotic
aka: Pila–Wilkie counting theorem, o-minimal structures, definable sets, rational points of bounded height, unlikely intersections, special points, André–Oort, Pila–Zannier strategy
- What: definable sets in o-minimal structures have few rational points off their algebraic parts.
- Fits when: unlikely intersections, special points.
- Lean: —
- Example: Pila's proof of André–Oort for products of modular curves ([Wikipedia: O-minimal theory](https://en.wikipedia.org/wiki/O-minimal_theory), [Wikipedia: André–Oort conjecture](https://en.wikipedia.org/wiki/André–Oort_conjecture)).
- See also: T531, T552

### T757 Geometric model theory of fields
`prove` · stage: argue · signals: logic, arithmetic-geometry, group
aka: Zilber trichotomy, stability theory, Mordell–Lang, function-field Diophantine geometry, algebraic groups, Hrushovski
- What: stability-theoretic classification (Zilber trichotomy) applied to algebraic groups.
- Fits when: function-field Diophantine geometry.
- Lean: —
- Example: Hrushovski's model-theoretic proof of the geometric Mordell–Lang conjecture in all characteristics ([Wikipedia: Ehud Hrushovski](https://en.wikipedia.org/wiki/Ehud_Hrushovski)).
- See also: T756

### T758 Stability and NIP regularity
`prove` `bound` · stage: argue · signals: graph, logic, dense
aka: stable regularity lemma, Malliaris–Shelah, NIP graphs, half-graphs, bounded VC dimension, regularity with no irregular pairs, polynomial-size partitions
- What: graphs definable in stable or NIP theories have regularity partitions with no irregular pairs or of polynomial size.
- Fits when: graphs without large half-graphs, bounded VC dimension.
- Lean: —
- Example: Malliaris–Shelah regularity lemma for stable graphs ([arXiv:1102.3904](https://arxiv.org/abs/1102.3904)).
- See also: T352, T371

### T759 Back-and-forth and Fraïssé limits
`prove` `find` · stage: argue · signals: logic, order, graph, symmetric
aka: back-and-forth method, Fraïssé limit, homogeneous structures, Rado graph, random graph, Cantor's isomorphism theorem, countable dense orders, universal objects
- What: builds or identifies countable homogeneous structures by extending partial isomorphisms.
- Fits when: uniqueness of countable structures, universal objects.
- Lean: Mathlib: `FirstOrder.Language.IsFraisseLimit`, `Order.iso_of_countable_dense` (Cantor).
- Example: the Rado graph and Cantor's theorem on countable dense orders ([Wikipedia: Back-and-forth method](https://en.wikipedia.org/wiki/Back-and-forth_method), [Wikipedia: Rado graph](https://en.wikipedia.org/wiki/Rado_graph), [Wikipedia: Fraïssé limit](https://en.wikipedia.org/wiki/Fraïssé_limit)).
- See also: T760, T761, T319

### T760 Ehrenfeucht–Fraïssé games
`prove` · stage: argue · signals: logic, game, impossibility
aka: EF games, back-and-forth games, elementary equivalence up to depth n, quantifier rank, first-order inexpressibility, connectivity, even cardinality, descriptive complexity
- What: a winning Duplicator strategy in the n-round game shows two structures agree on all sentences of quantifier depth n.
- Fits when: proving inexpressibility in first-order logic.
- Lean: an n-round game on two small finite structures is a finite game, decidable by `decide +kernel`.
- Example: the standard method for proving properties (connectivity, even cardinality) are not first-order expressible ([Wikipedia: Ehrenfeucht–Fraïssé game](https://en.wikipedia.org/wiki/Ehrenfeucht–Fraïssé_game)).
- See also: T759, T761, T1036

### T761 Zero-one laws
`prove` · stage: argue · signals: logic, random, graph, threshold
aka: Glebskii–Fagin 0-1 law, first-order properties of random graphs, almost sure theories, extension axioms, Rado graph
- What: every first-order graph property has random-graph probability tending to 0 or 1.
- Fits when: asymptotic logical properties of random structures.
- Lean: —
- Example: Glebskii et al./Fagin 0-1 law via the Rado graph ([Wikipedia: Zero-one law (logic)](https://en.wikipedia.org/wiki/Zero-one_law_%28logic%29)).
- See also: T759, T775

### T762 Forcing and independence
`prove` · stage: argue · signals: logic, impossibility
aka: Cohen forcing, independence from ZFC, consistency proofs, generic extensions, Whitehead problem, continuum hypothesis
- What: builds models where a statement fails, to show it is unprovable.
- Fits when: a combinatorial or analytic statement resists all approaches and might be independent.
- Lean: —
- Example: Shelah's proof that the Whitehead problem is independent of ZFC ([Wikipedia: Forcing](https://en.wikipedia.org/wiki/Forcing_%28mathematics%29), [Wikipedia: Whitehead problem](https://en.wikipedia.org/wiki/Whitehead_problem)).
- See also: T763, T765

### T763 Combinatorial principles as hypotheses
`prove` · stage: reformulate · signals: logic
aka: Martin's axiom, MA, diamond principle, ◊, continuum hypothesis, CH constructions, exotic sets, infinite combinatorics
- What: settles a statement under an extra axiom first, then asks whether ZFC suffices.
- Fits when: infinite combinatorics and topology questions.
- Lean: a result under CH is a Lean theorem with CH as a hypothesis, not an axiom.
- Example: CH-based constructions of exotic sets; Martin's axiom; the diamond principle ([Tricki: How to use the continuum hypothesis](https://www.tricki.org/article/How_to_use_the_continuum_hypothesis), [Wikipedia: Martin's axiom](https://en.wikipedia.org/wiki/Martin's_axiom), [Wikipedia: Diamond principle](https://en.wikipedia.org/wiki/Diamond_principle)).
- See also: T762

### T764 Ordinal assignments for termination and independence
`prove` · stage: argue · signals: logic, order, sequence
aka: ordinal measures, ε₀, Goodstein's theorem, Paris–Harrington, hydra games, termination proofs, unprovability in PA
- What: maps states to ordinals that decrease at each step.
- Fits when: termination of processes with nested growth; independence from PA.
- Lean: termination by a well-founded measure (`termination_by`); Mathlib has `Ordinal`, the notation system `ONote` and hydra-game termination (Logic/Hydra.lean).
- Example: Goodstein's theorem (unprovable in PA); Paris–Harrington ([Wikipedia: Goodstein's theorem](https://en.wikipedia.org/wiki/Goodstein's_theorem), [Wikipedia: Paris–Harrington theorem](https://en.wikipedia.org/wiki/Paris–Harrington_theorem)).
- See also: T330, T766, T23

### T765 Ordinal analysis and reverse mathematics
`prove` · stage: judge · signals: logic
aka: reverse mathematics, subsystems of second-order arithmetic, RCA₀, ACA₀, proof-theoretic strength, minimal hypotheses, Kruskal's theorem, Ramsey's theorem
- What: measures exactly which axioms a theorem needs.
- Fits when: finding minimal hypotheses; extracting bounds; deciding what Lean's library must provide.
- Lean: —
- Example: reverse-mathematics classification of Ramsey's theorem and Kruskal's theorem ([Wikipedia: Reverse mathematics](https://en.wikipedia.org/wiki/Reverse_mathematics), [Wikipedia: Ordinal analysis](https://en.wikipedia.org/wiki/Ordinal_analysis)).
- See also: T764, T769

### T766 Well-quasi-orders and minimal bad sequences
`prove` · stage: argue · signals: order, graph, sequence
aka: wqo, minimal bad sequence, Higman's lemma, Kruskal's tree theorem, Nash-Williams, finite obstruction sets, graph minors, termination
- What: a minimal bad sequence argument shows every infinite sequence has an increasing pair.
- Fits when: finiteness of obstruction sets, termination.
- Lean: Mathlib: `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` (Higman's lemma).
- Example: Higman's lemma; Nash-Williams' proof of Kruskal's tree theorem ([Wikipedia: Higman's lemma](https://en.wikipedia.org/wiki/Higman's_lemma), [Wikipedia: Kruskal's tree theorem](https://en.wikipedia.org/wiki/Kruskal's_tree_theorem), [Wikipedia: Well-quasi-ordering](https://en.wikipedia.org/wiki/Well-quasi-ordering)).
- See also: T468, T764, T334

### T767 Zorn's lemma and transfinite induction
`prove` `find` · stage: construct · signals: logic, construction
aka: Zorn's lemma, transfinite recursion, well-ordering, maximal objects, Hamel basis, Cauchy functional equation, continuum-many requirements
- What: builds maximal objects, or constructs sets by transfinite recursion meeting continuum-many requirements.
- Fits when: the construction never finishes in countably many steps.
- Lean: Mathlib: `zorn_subset`, `Basis.ofVectorSpace` (Hamel bases); transfinite induction is well-founded recursion on `Ordinal`.
- Example: Hamel bases and nonlinear additive functions ([Tricki: How to use Zorn's lemma](https://www.tricki.org/article/How_to_use_Zorns_lemma), [Wikipedia: Transfinite induction](https://en.wikipedia.org/wiki/Transfinite_induction), [Wikipedia: Hamel basis](https://en.wikipedia.org/wiki/Hamel_basis)).
- See also: T763

### T768 Incompressibility
`prove` `bound` · stage: argue · signals: computation, random, inequality, resource-bound
aka: Kolmogorov complexity, incompressibility method, random strings, average-case lower bounds, description length, Shellsort average case, Heilbronn triangle problem
- What: a random string cannot be compressed, so a hypothetical short description yields a contradiction.
- Fits when: average-case lower bounds, combinatorial existence.
- Lean: the counting core (fewer than 2^n strings shorter than n bits) by `Finset.card` lemmas.
- Example: the incompressibility method for lower bounds, e.g. Shellsort's average case and Heilbronn's triangle problem ([Wikipedia: Incompressibility method](https://en.wikipedia.org/wiki/Incompressibility_method)).
- See also: T374, T381, T1043

### T769 Proof mining and Herbrand-type extraction
`bound` · stage: argue · signals: logic, analytic
aka: proof mining, Kohlenbach, Herbrand's theorem, Herbrand disjunction, functional interpretation, rates of convergence, metastability, effective bounds from ineffective proofs
- What: extracts explicit bounds from ineffective proofs by proof-theoretic transformations.
- Fits when: you have a qualitative proof and need effective constants.
- Lean: the extracted bound is an ordinary statement proved again in Lean.
- Example: Kohlenbach's proof mining in analysis; Herbrand's theorem ([Wikipedia: Proof mining](https://en.wikipedia.org/wiki/Proof_mining), [Wikipedia: Herbrand's theorem](https://en.wikipedia.org/wiki/Herbrand's_theorem)).
- See also: T314, T313, T324

### T770 Craig interpolation
`prove` · stage: argue · signals: logic
aka: interpolants, Lyndon interpolation, common-language separation, definability theorems
- What: if A ⊢ B, a formula in their common language lies between them.
- Fits when: definability results, separating hypotheses.
- Lean: —
- Example: Craig's 1957 proof for first-order logic, with Lyndon's 1959 strengthening (polarity-respecting interpolants) ([Wikipedia: Craig interpolation](https://en.wikipedia.org/wiki/Craig_interpolation)).
- See also: T760

### T771 Undecidability by encoding computation
`prove` · stage: argue · signals: computation, logic, group, impossibility
aka: reduction from the halting problem, universal machines, Hilbert's tenth problem, Matiyasevich, MRDP, word problem for groups, Novikov–Boone, Conway's generalized Collatz, conjecture-as-halting encoding
- What: embeds a universal machine to show that no algorithm decides a class of problems.
- Fits when: a family of problems seems to need case-by-case ingenuity forever; algorithmic questions about all finitely presented objects.
- Lean: Mathlib: `ComputablePred.halting_problem`, `ComputablePred.rice`; `Dioph.pow_dioph` (exponentiation is Diophantine, part of Matiyasevich's theorem).
- Example: Matiyasevich's resolution of Hilbert's tenth problem; Conway's undecidable generalizations of Collatz ([Wikipedia: Hilbert's tenth problem](https://en.wikipedia.org/wiki/Hilbert's_tenth_problem), [Wikipedia: Collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture)); Novikov–Boone undecidability of the word problem ([Wikipedia: Word problem for groups](https://en.wikipedia.org/wiki/Word_problem_for_groups)).
- See also: T343, T578, T37, T1010

### T772 Descriptive (Borel) combinatorics
`prove` `find` · stage: argue · signals: graph, colouring, logic, geometry
aka: Borel combinatorics, measurable colourings, definable graphs, Borel chromatic number, equidecomposition, Tarski circle squaring
- What: asks for definable (Borel, measurable) solutions; ergodic and graph-theoretic tools interact.
- Fits when: equidecomposition, colourings of definable graphs.
- Lean: —
- Example: Marks–Unger Borel circle squaring ([arXiv:1612.05833](https://arxiv.org/abs/1612.05833)).
- See also: T666, T773

### T773 Determinacy and infinite games
`prove` · stage: argue · signals: game, logic, topology
aka: Borel determinacy, Gale–Stewart games, Banach–Mazur game, meagre sets, Baire property, regularity of definable sets
- What: winning strategies for definable games yield regularity properties of sets.
- Fits when: Baire property, measurability of definable sets.
- Lean: —
- Example: Martin's Borel determinacy; Banach–Mazur games characterizing meagre sets ([Wikipedia: Borel determinacy theorem](https://en.wikipedia.org/wiki/Borel_determinacy_theorem), [Wikipedia: Banach–Mazur game](https://en.wikipedia.org/wiki/Banach–Mazur_game)).
- See also: T772, T822

### T774 Ultrafilter limits
`prove` · stage: argue · signals: colouring, logic, additive
aka: nonprincipal ultrafilters, ultralimits, idempotent ultrafilters, Hindman's theorem, infinite Ramsey theorem, homogeneous sub-objects, Banach limits
- What: a nonprincipal ultrafilter gives a limit of every bounded sequence and an infinite Ramsey theorem.
- Fits when: extracting convergent or homogeneous sub-objects uniformly.
- Lean: Mathlib: `Ultrafilter`; Hindman's theorem `Hindman.FP_partition_regular`.
- Example: Ramsey's theorem and Hindman's theorem via ultrafilters ([Tricki: How to use ultrafilters](https://www.tricki.org/article/How_to_use_ultrafilters), [Wikipedia: Ultrafilter](https://en.wikipedia.org/wiki/Ultrafilter)).
- See also: T433, T753
