# Proof strategies
General moves for an open problem: specialize, generalize, reformulate, strengthen, embed, dualize, compactify, and reduce to a finite check.

### T300 Specialize
`prove` `find` · stage: reformulate · signals: induction-stuck
aka: small cases, extreme cases, simplest nontrivial instance, limiting parameter value, specialise, Gel'fond's question, smallest resisting case
- What: solve the simplest nontrivial instance or a limiting parameter value, then read the general proof or the obstruction off it.
- Fits when: the general statement is opaque but has natural parameters (n, k, dimension, field size).
- Lean: small instances by `decide +kernel` or `norm_num`; they also test the statement before a proof (T136).
- Example: Gel'fond's "what is the simplest nontrivial example?"; Hilbert called specialization "one of the most important levers" ([Tricki: Look at small cases](https://www.tricki.org/article/Look_at_small_cases), [Tricki: Do an extreme case first](https://www.tricki.org/article/Do_an_extreme_case_first), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T301, T309, T1367, T136

### T301 Generalize
`prove` · stage: reformulate · signals: induction-stuck
aka: inventor's paradox, generalise, more general problem, add parameters, abstraction, "make it more complicated", Macdonald polynomials
- What: replace the problem by a more general or more abstract one whose extra freedom or cleaner structure makes the proof go through.
- Fits when: the statement is one value of a natural family, or irrelevant concrete detail hides the mechanism.
- Lean: state and prove the general theorem, then get the original as a corollary by `exact` with specific arguments.
- Example: Macdonald polynomials arose by adding parameters to Jack and Hall–Littlewood polynomials; "if you can't prove it, make it more complicated" ([MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks), [Tricki: Simplify your problem by generalizing it](https://www.tricki.org/article/Simplify_your_problem_by_generalizing_it)).
- See also: T300, T302, T303, T319, T1367

### T302 Strengthen the induction hypothesis
`prove` · stage: argue · signals: induction-stuck
aka: strengthen the statement, load the induction, stronger inductive claim, precoloured boundary, 5-choosability of planar graphs, list colouring, Milin conjecture, Robertson conjecture, Bieberbach conjecture
- What: prove a stronger statement that reproduces itself on substructures, so the inductive step closes.
- Fits when: induction almost works but the hypothesis is too weak to hand down.
- Lean: make the strengthened claim the theorem and use `induction … generalizing`; `Nat.strong_induction_on` for strong induction.
- Example: Thomassen's proof that every planar graph is 5-choosable, inducting on a stronger statement with precoloured outer vertices ([Tricki: Strengthen your inductive hypothesis](https://www.tricki.org/article/Strengthen_your_inductive_hypothesis), [Wikipedia: List coloring](https://en.wikipedia.org/wiki/List_coloring)); de Branges proved the stronger Milin conjecture, which implies Robertson's and Bieberbach's ([Wikipedia: de Branges's theorem](https://en.wikipedia.org/wiki/De_Branges%27s_theorem)).
- See also: T301, T334, T335, T464

### T303 Embed in a family; add a parameter
`prove` `compute` · stage: reformulate · signals: analytic, identity
aka: Feynman's trick, differentiation under the integral sign, deformation, interpolation in a parameter, one-parameter family, treat an object as one of a family
- What: treat the object as one member of a family, then differentiate, deform or interpolate in the parameter.
- Fits when: one object is rigid, but the family has an easy member or a derivative identity.
- Lean: Mathlib: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiates under the integral sign.
- Example: Feynman's trick of differentiating under the integral sign to evaluate integrals ([Tricki: treat an object as one of a family](https://www.tricki.org/article/To_understand_an_object_consider_treating_it_as_one_of_a_family_of_objects_and_analysing_the_family), [Tricki: differentiate under the integral sign](https://www.tricki.org/article/To_evaluate_an_integral_differentiate_under_the_integral_sign)).
- See also: T301, T321, T319

### T304 Reformulate in another domain
`prove` `find` `bound` `compute` · stage: reformulate
aka: crossover, translation into another formalism, change the question, translate into a field with other tools, equivalent forms, graph, matrix, polynomial or incidence version, sensitivity conjecture, MRDP, Keller graphs, Kadison–Singer, Anderson paving, Weaver's conjecture, Frey curve
- What: restate the problem as a graph, matrix, polynomial, group or geometry problem where strong tools exist.
- Fits when: native tools stall but the structure has a known shadow elsewhere; collect the known equivalent forms and pick the one closest to a toolbox.
- Lean: prove the equivalence in Lean once; then either side counts. A solver encoding is T119.
- Example: Huang's proof of the Sensitivity Conjecture: Boolean sensitivity became induced subgraphs of the cube, then eigenvalues of a signed adjacency matrix plus Cauchy interlacing ([arXiv:1907.00847](https://arxiv.org/abs/1907.00847)), after Gotsman–Linial's reduction ([Quanta](https://www.quantamagazine.org/mathematician-solves-computer-science-conjecture-in-two-pages-20190725/)); Elekes–Sharir turned distinct distances into line incidences in R³ ([arXiv:1011.4105](https://arxiv.org/abs/1011.4105)); Frey's curve turned Fermat into modularity ([Wikipedia: Wiles's proof](https://en.wikipedia.org/wiki/Wiles%27s_proof_of_Fermat%27s_Last_Theorem)); Keller's conjecture as cliques in Keller graphs ([Wikipedia: Keller's conjecture](https://en.wikipedia.org/wiki/Keller%27s_conjecture)).
- See also: T400, T524, T119, T1001, T310

### T305 Auxiliary object
`prove` `bound` · stage: argue · signals: polynomial, finite-field, impossibility
aka: auxiliary polynomial, auxiliary function, auxiliary graph, auxiliary measure, vanishing/nonvanishing dichotomy, Kakeya sets over finite fields
- What: introduce an object absent from the statement (polynomial, function, graph, measure) whose properties force the conclusion.
- Fits when: something must be shown small or absent, and a vanishing/nonvanishing dichotomy is available.
- Lean: polynomial vanishing via Mathlib's `Polynomial.card_roots'` and `MvPolynomial`; the rest depends on the object.
- Example: Dvir's finite-field Kakeya theorem: a low-degree polynomial vanishing on a small Kakeya set must vanish identically ([arXiv:0803.2336](https://arxiv.org/abs/0803.2336)).
- See also: T393, T391, T541, T543

### T306 Work backwards
`prove` `find` · stage: reformulate
aka: penultimate step, working backwards, Pappus' analysis, last line first, which lemma gives it, related problem
- What: assume the goal, ask what would immediately imply it, and chain back to the data.
- Fits when: the target has a recognizable final form (an identity, an inequality, the last step of a construction).
- Lean: goal-directed by nature: `refine` with `?_` holes, `suffices`, `apply` and lemma search (T135).
- Example: Pólya's heuristics "work backwards" and "do you know a related problem?" ([Wikipedia: How to Solve It](https://en.wikipedia.org/wiki/How_to_Solve_It)).
- See also: T307, T135

### T307 Prove a consequence first
`prove` · stage: practice
aka: intermediate lemma, weaker shadow, independence of a parameter, evaluate at one value, factor the implication
- What: factor A ⇒ B through an easier consequence C of B, then prove A ∧ C ⇒ B, or mine the proof of C for B.
- Fits when: B is strong and a weaker shadow (independence of a parameter, a special value) is reachable.
- Lean: C as its own lemma, then `have hC := …` inside the proof of B.
- Example: proving an identity by first showing an expression is independent of a parameter, then evaluating it at one value ([Tricki: Prove a consequence first](https://www.tricki.org/article/Prove_a_consequence_first)).
- See also: T306, T323

### T308 Assume a missing hypothesis, remove it later
`prove` · stage: reformulate · signals: additive
aka: assume the hypothesis for now, conditional argument, structured versus uniform case, wishful thinking, Roth's theorem
- What: run the promising argument under an extra assumption (smoothness, periodicity, structure), then eliminate it.
- Fits when: a tool needs a hypothesis the problem lacks, and you need to see whether the rest of the argument works.
- Lean: prove the conditional lemma `h → goal` first; removing `h` is a separate lemma.
- Example: Roth's theorem, the Tricki's "poster child": first argue as if the set were Fourier-uniform or structured, then handle the other case ([Tricki: assume the hypothesis for now](https://www.tricki.org/article/If_an_argument_looks_promising_but_needs_a_hypothesis_assume_the_hypothesis_for_now_but_try_to_remove_it_later)).
- See also: T412, T413

### T309 Finite-field model first
`prove` `bound` · stage: reformulate · signals: finite-field, additive
aka: model setting first, toy models, F_p^n model, function-field model, dyadic model, cap sets, finite-field Kakeya, Wolff's problem, Roth and Bogolyubov programmes
- What: solve the analogue in F_p^n (or a function field) where subgroups replace progressions and Fourier analysis is exact, then transfer.
- Fits when: additive or analytic problems over Z/N are drowned in Bohr-set and error-term technicalities; the integers carry noise that hides the mechanism.
- Lean: finite-field models are concrete: Mathlib's `ZMod p` and `GaloisField`; small cases by `decide +kernel`.
- Example: Meshulam's cap-set bound and the F_p^n models surveyed by Green guided the integer Roth and Bogolyubov programmes ([arXiv:math/0409420](https://arxiv.org/abs/math/0409420)); Wolff posed finite-field Kakeya hoping its methods would transfer, Dvir solved it, while R³ needed other ideas (Wang–Zahl 2025) ([Wikipedia: Kakeya set](https://en.wikipedia.org/wiki/Kakeya_set)); Kelley–Meka ([arXiv:2302.05537](https://arxiv.org/abs/2302.05537)).
- See also: T310, T395, T420, T393

### T310 Hunt for analogies
`prove` · stage: reformulate · signals: arithmetic-geometry, polynomial
aka: analogy, number fields versus function fields, Rosetta stone, Weil's letter, Mason–Stothers, abc for polynomials, Weil conjectures, positive, negative and neutral analogy, critical disanalogy
- What: solve the analogue where an extra tool exists (derivatives, geometry, Frobenius), then seek its arithmetic counterpart.
- Fits when: a problem over Z has a polynomial or curve analogue.
- Lean: Mathlib: `Polynomial.abc` (Mason–Stothers) in `NumberTheory/FLT/MasonStothers.lean`.
- Example: the Mason–Stothers theorem (abc for polynomials, via derivatives) as a model for abc; the Weil conjectures as the Riemann hypothesis over finite fields ([Wikipedia: Mason–Stothers theorem](https://en.wikipedia.org/wiki/Mason–Stothers_theorem), [Wikipedia: Weil conjectures](https://en.wikipedia.org/wiki/Weil_conjectures)); Weil's 1940 "Rosetta stone" letter; Keynes and Hesse on positive, negative and neutral analogy ([SEP: Analogy](https://plato.stanford.edu/entries/reasoning-analogy/)).
- See also: T309, T304

### T311 Let the best construction predict the proof
`bound` · stage: judge · signals: additive, asymptotic
aka: lower-bound examples guide upper bounds, Behrend's construction, exp(c√log n) bounds, power-saving bounds, choosing between density increment and polynomial method
- What: the shape of the best lower-bound example tells which bound types (power, exp(c√log n)) a technique can give.
- Fits when: choosing between density increment, polynomial method, energy increment, etc.
- Lean: —
- Example: Behrend's 3-AP-free set of density exp(-c√log N) rules out power-saving bounds for Roth's theorem ([Tricki: what a lower bound says](https://www.tricki.org/article/what_a_lower_bound_can_say_about_the_proof_of_the_upper_bound), [Tricki: how exp(c(log n)^½) arises](https://www.tricki.org/article/How_does_a_bound_of_expclog_n12_ever_arise)).
- See also: T424, T412, T312

### T312 Probabilistic heuristic model
`prove` `bound` · stage: explore · signals: random, pseudorandom
aka: Cramér's model of primes, random graph heuristic, predicted constants, sanity check, "if extremal examples look spread out, try a random one"
- What: predict the truth and its constants with a random model (random graph, Cramér's model of primes), then prove or test against it.
- Fits when: you need a conjecture to aim at or a sanity check on a claimed bound.
- Lean: — (a prediction proves nothing).
- Example: the Tricki's heuristics for guessing probabilistic estimates; Gowers' principle "if extremal examples look spread out, try a random one" ([Tricki: heuristic principles](https://www.tricki.org/article/Useful_heuristic_principles_for_guessing_probabilistic_estimates), [Gowers: two cultures](https://www.dpmms.cam.ac.uk/~wtg10/2cultures.pdf)).
- See also: T374, T311

### T313 Compactness and contradiction
`prove` `bound` · stage: argue · signals: analytic, logic
aka: finite convergence principle, metastability, uniform bounds from qualitative theorems, sequence of counterexamples, limit object, soft versus hard analysis
- What: get a uniform finite statement from an infinitary one by assuming a sequence of counterexamples and passing to a limit object.
- Fits when: a qualitative infinite theorem is known and you need the existence of a uniform bound.
- Lean: Mathlib: `tendsto_subseq_of_bounded` (Bolzano–Weierstrass); the bound obtained is ineffective, so no finite check can evaluate it.
- Example: the finite convergence (metastability) principle as the finitary form of "bounded monotone sequences converge" ([Tricki: compactness and contradiction](https://www.tricki.org/article/Use_the_compactness_and_contradiction_method_to_derive_finitary_quantitative_results_from_infinitary_qualitative_ones), [Tao: soft vs hard analysis](https://terrytao.wordpress.com/2007/05/23/soft-analysis-hard-analysis-and-the-finite-convergence-principle/)).
- See also: T314, T318, T751

### T314 Quantify the qualitative
`prove` `bound` · stage: argue · signals: analytic, asymptotic
aka: effective constants, explicit dependencies, finitary versions, Bourgain's toolkit, hard analysis
- What: replace "converges" or "is bounded" by explicit statements with parameters, so pigeonholing and iteration become possible.
- Fits when: an infinitary proof hides dependencies; you need effective constants (which Lean needs anyway).
- Lean: explicit constants make the final numeric step checkable by `norm_num`.
- Example: Bourgain's habit of quantifying qualitative problems, in Tao's study of his toolkit ([arXiv:2009.06736](https://arxiv.org/abs/2009.06736)).
- See also: T313, T324, T620

### T315 Look for the group
`prove` `compute` · stage: argue · signals: group, symmetric
aka: symmetry group, Weil's slogan, group acting on a finite set, Cauchy's theorem, Sylow theorems, averaging over a group, isotypic decomposition
- What: find the symmetry group behind the difficulty; reduce by it, average over it, or decompose into its isotypic pieces.
- Fits when: the problem is invariant under transformations, or a count or identity looks too regular to be accidental.
- Lean: Mathlib: `MulAction`, `card_modEq_card_fixedPoints` (p-group actions), `Sylow`.
- Example: Weil's slogan "where there is a difficulty, look for the group", and proofs by letting a group act on a finite set (Cauchy, Sylow) ([MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks), [Tricki: group acting on a finite set](https://www.tricki.org/article/Proving_results_by_letting_a_group_act_on_a_finite_set)).
- See also: T344, T455, T563, T29

### T316 Dualize
`bound` `prove` · stage: reformulate · signals: inequality, geometry
aka: LP duality, convex duality, Fourier side, adjoint, Poincaré duality, packing/covering duality, Cohn–Elkies bound, sphere packing in dimension 8, Viazovska
- What: pass to the dual problem (LP/convex dual, Fourier side, adjoint, Poincaré duality) whose feasible points certify bounds for the primal.
- Fits when: a max/min problem, a packing/covering pair, or an existence/obstruction pair.
- Lean: a dual feasible point is a certificate; exact rational duals check by `norm_num` and `linarith` (T48).
- Example: the Cohn–Elkies linear programming bound, made sharp in dimension 8 by Viazovska's modular-form auxiliary function ([arXiv:math/0110009](https://arxiv.org/abs/math/0110009), [arXiv:1603.04246](https://arxiv.org/abs/1603.04246)).
- See also: T48, T50, T470

### T317 Enlarge the solution space, then regain regularity
`prove` · stage: argue · signals: pde, analytic
aka: weak solutions, generalized solutions, Sobolev spaces, regularity theory, Hilbert's 19th problem, De Giorgi–Nash
- What: define weak or generalized solutions so existence is easy, then prove the solution is nice.
- Fits when: smooth existence is hard but limits exist in a weaker sense.
- Lean: —
- Example: Hilbert's 19th problem: minimizers exist in Sobolev spaces; De Giorgi and Nash proved they are smooth ([Wikipedia: Hilbert's nineteenth problem](https://en.wikipedia.org/wiki/Hilbert's_nineteenth_problem)).
- See also: T673, T676, T682

### T318 Compactify
`prove` · stage: argue · signals: topology, geometry
aka: add limit objects, degenerations, boundary of a moduli space, one-point compactification, Gromov–Hausdorff convergence, Gromov's compactness theorem
- What: add degenerate limit objects so sequences converge, then study the boundary.
- Fits when: sequences or moduli escape to infinity or degenerate.
- Lean: Mathlib: `OnePoint` (one-point compactification); Gromov–Hausdorff space in `Topology/MetricSpace/GromovHausdorff.lean`.
- Example: Gromov's compactness theorem for manifolds with Ricci and diameter bounds under Gromov–Hausdorff convergence ([Wikipedia: Gromov–Hausdorff convergence](https://en.wikipedia.org/wiki/Gromov–Hausdorff_convergence), [MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T313, T774

### T319 Universal object
`prove` · stage: reformulate · signals: group, polynomial
aka: free group, free object, generic point, universal property, bundle a family into one object, "try it for the free group"
- What: replace a question about all objects of a type by one question about the universal (free, generic) object, then specialize.
- Fits when: the property is preserved under quotients or specialization.
- Lean: Mathlib: `FreeGroup`, `MvPolynomial` with `MvPolynomial.aeval` to specialize.
- Example: the group-theory habit "try it for the free group" ([Tricki: Bundle a family into a universal object](https://www.tricki.org/article/Bundle_a_family_of_objects_into_a_single_universal_object)).
- See also: T301, T598

### T320 Divide and conquer
`prove` `bound` · stage: argue · signals: analytic, pseudorandom
aka: decompose by size, frequency or scale, structure versus randomness, case split by magnitude, high and low frequencies
- What: decompose into components each dominated by one feature (scale, frequency, structure vs noise), control each, and sum.
- Fits when: an object mixes behaviours that need different tools.
- Lean: split sums with Mathlib's `Finset.sum_filter_add_sum_filter_not`; case splits by `rcases le_or_lt a b`.
- Example: linear estimates split by size or frequency; the structure/randomness dichotomy ([Tricki: Divide and conquer](https://www.tricki.org/article/Divide_and_conquer), [arXiv:math/0512114](https://arxiv.org/abs/math/0512114)).
- See also: T413, T620, T632

### T321 Continuity method and bootstrap
`prove` · stage: argue · signals: pde, analytic
aka: method of continuity, a priori estimates, open-closed-nonempty argument, continuous induction, bootstrap argument, implicit function theorem, nonlinear elliptic existence
- What: show the set of parameters where the result holds is nonempty, open and closed; or assume a bound and derive a strictly better one.
- Fits when: a problem deforms continuously into a solved one (openness by the implicit function theorem, closedness by a priori estimates); an estimate seems to need itself.
- Lean: Mathlib: `IsClopen.eq_univ` for the connectedness step; `HasStrictFDerivAt.implicitFunction` for openness.
- Example: a real-analytic function vanishing to infinite order at one point vanishes identically (the set where it does is open, closed and nonempty) ([Tricki: Use the continuity method](https://www.tricki.org/article/Use_the_continuity_method), [Tricki: implicit function theorem](https://www.tricki.org/article/Use_the_implicit_function_theorem_to_prove_smoothness)).
- See also: T303, T674, T670

### T322 Invert
`prove` · stage: reformulate · signals: analytic
aka: inversion, "man muss immer umkehren", inverse function, inverse problem, reversed inequality, attack the negation, elliptic functions
- What: study the inverse function, inverse problem or reversed inequality.
- Fits when: the forward map is multivalued or messy and its inverse is single-valued or analytic.
- Lean: Mathlib: `Function.invFun`, `HasStrictDerivAt.to_localInverse` for local inverses.
- Example: Abel and Jacobi inverting elliptic integrals to obtain elliptic functions ([MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T323, T1370

### T323 Think about the converse
`prove` · stage: practice
aka: converse, necessary conditions, what any proof must use, constrain the proof strategy
- What: work out what the converse would need; it constrains what any proof of the original must use.
- Fits when: a proof attempt has too much freedom.
- Lean: —
- Example: the Tricki's research-case discussion ([Tricki: Think about the converse](https://www.tricki.org/article/Think_about_the_converse)).
- See also: T307, T322

### T324 Reduce to a finite check
`prove` `compute` · stage: argue · signals: integers, analytic
aka: effective bounds then exhaustive check, finite check plus explicit analytic tail, explicit constants, Baker bounds, explicit circle method, explicit Chabauty, ternary Goldbach, Fibonacci perfect powers, Kepler conjecture, Catalan's conjecture, Keller's conjecture
- What: make an ineffective "for large n" effective with explicit constants, then check every case below the bound.
- Fits when: Diophantine, additive or analytic statements with explicit constants; the infinite problem has a compactness or bound argument.
- Lean: the analytic tail needs a formal proof; the finite part counts only if N stays kernel-small (T42, T121, T122), so push the analysis to make N small.
- Example: Fibonacci perfect powers ([arXiv:math/0403046](https://arxiv.org/abs/math/0403046)); ternary Goldbach: Helfgott's analysis for large n ([arXiv:1312.7748](https://arxiv.org/abs/1312.7748)) with the Helfgott–Platt check below it ([arXiv:1305.3062](https://arxiv.org/abs/1305.3062)); Fejes Tóth's reduction for Kepler ([Wikipedia: Kepler conjecture](https://en.wikipedia.org/wiki/Kepler_conjecture)); Tijdeman's bound for Catalan via Baker's method ([Wikipedia: Catalan's conjecture](https://en.wikipedia.org/wiki/Catalan%27s_conjecture)); Corrádi–Szabó for Keller ([Wikipedia: Keller's conjecture](https://en.wikipedia.org/wiki/Keller%27s_conjecture)).
- See also: T42, T121, T122, T481, T537
