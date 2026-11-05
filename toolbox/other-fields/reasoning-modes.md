# Reasoning modes
Ways to infer and weigh claims short of proof: abduction, estimation, plausible reasoning, diagnosis and guessing part of the answer.

### T1322 Abduction
`prove` · stage: explore
aka: inference to the best explanation, Peirce, surprising fact, numerical coincidence, posit a structure, monstrous moonshine, 196884 = 196883 + 1, McKay, Le Verrier, Neptune
- What: from a surprising fact C and "if A, then C", suspects A; Peirce's only source of new ideas.
- Fits when: a numerical coincidence appears; posit the structure that would explain it, then test new consequences.
- Lean: —
- Example: Le Verrier inferred Neptune from Uranus's anomalies ([Wikipedia: Discovery of Neptune](https://en.wikipedia.org/wiki/Discovery_of_Neptune); [Wikipedia: Abductive reasoning](https://en.wikipedia.org/wiki/Abductive_reasoning)); McKay's 196884 = 196883 + 1 started moonshine ([Wikipedia: Monstrous moonshine](https://en.wikipedia.org/wiki/Monstrous_moonshine)).
- See also: T1328, T1329

### T1323 Fermi estimation
`find` `prove` `bound` `compute` · stage: judge
aka: Fermi problem, order-of-magnitude estimate, back-of-the-envelope, search-space size, run-time estimate, first-moment sanity check, does it fit this PC, Trinity
- What: chains order-of-magnitude guesses; overestimates and underestimates partly cancel.
- Fits when: before computing: counts, search-space sizes and run times; a first-moment sanity check of a conjecture; whether a `compute` run fits this PC.
- Lean: —
- Example: Fermi estimated the Trinity yield from "pieces of paper he dropped" ([Wikipedia: Fermi problem](https://en.wikipedia.org/wiki/Fermi_problem)).
- See also: T154, T1300, T1303

### T1324 Plausible reasoning and Bayesian updating
`find` `prove` `bound` `compute` · stage: explore
aka: Pólya, patterns of plausible inference, credence, odds, Bayesian epistemology, weighing evidence, true or false, which side to work on
- What: credences move with evidence; a verified consequence unlike earlier ones raises credibility most.
- Fits when: the truth value is in doubt; keep explicit odds on true vs false, update on small cases, numerics and special cases, spend most effort on the likelier side and some on the other.
- Lean: —
- Example: Pólya's patterns of plausible inference ([Wikipedia: Mathematics and Plausible Reasoning](https://en.wikipedia.org/wiki/Mathematics_and_Plausible_Reasoning); [Wikipedia: Bayesian epistemology](https://en.wikipedia.org/wiki/Bayesian_epistemology)).
- See also: T1327, T1353, T1370

### T1325 Differential diagnosis
`find` `prove` `bound` `compute` · stage: practice
aka: competing hypotheses, rank by probability and cost of missing, discriminating test, likelihood ratio, why does the method fail, is it true
- What: lists candidate explanations, ranks them by probability and cost of missing, and runs the test that best separates them; updates by likelihood ratios.
- Fits when: asking why a method fails, or whether a claim is true; choose the cheapest discriminating experiment.
- Lean: —
- Example: [Wikipedia: Differential diagnosis](https://en.wikipedia.org/wiki/Differential_diagnosis).
- See also: T1352, T1369

### T1326 Cribs
`find` `bound` · stage: construct · signals: construction
aka: crib, known-plaintext attack, Bletchley, Champollion, cartouches, guess part of the answer, ansatz, assumed symmetry, small support, group action, algebraic form, FunSearch symmetries
- What: guesses a fragment of the answer and tests whether the rest falls out.
- Fits when: an extremal object is sought; assume structure in it (symmetry, small support, group action, algebraic form) to shrink the search; a guess that works is a lead for a proof.
- Lean: the object found is checked like any witness (T118).
- Example: Bletchley cribs ([Wikipedia: Known-plaintext attack](https://en.wikipedia.org/wiki/Known-plaintext_attack)); Champollion's cartouches ([Wikipedia: Decipherment of ancient Egyptian scripts](https://en.wikipedia.org/wiki/Decipherment_of_ancient_Egyptian_scripts)); FunSearch users saw symmetries in top programs and built them in ([DeepMind](https://deepmind.google/discover/blog/funsearch-making-new-discoveries-in-mathematical-sciences-using-large-language-models/)).
- See also: T27, T107, T118

### T1377 Gaps in a classification table
`find` `prove` · stage: explore · signals: classification, construction
aka: periodic table, Mendeleev, eka-elements, predicted objects, missing entries, feasible parameters, parameter tables, sporadic groups, Lyons group, Moore graphs, degree 57, strongly regular graph tables, fill the gap
- What: arranges the known objects by their invariants until a pattern shows; a cell the pattern allows but no known object fills is a predicted object with predicted invariants, which become the constraints of a `find` search or the target of an impossibility proof.
- Fits when: a classification has a table (by order, parameters, degree) whose rows obey a rule; list the feasible but unrealized entries and attack the most constrained one.
- Lean: — for the prediction; a found object is a witness (T118), an empty cell an impossibility proof.
- Example: Mendeleev predicted eka-aluminium, eka-boron and eka-silicon with atomic weights and densities; gallium (1875), scandium (1879) and germanium (1886) matched, while other predictions failed ([Wikipedia: Mendeleev's predicted elements](https://en.wikipedia.org/wiki/Mendeleev%27s_predicted_elements)); Lyons derived the only possible order of a simple group with a given involution centralizer, and Sims proved the group exists with machine calculations ([Wikipedia: Lyons group](https://en.wikipedia.org/wiki/Lyons_group)); Hoffman–Singleton left degrees 2, 3, 7 and 57 for diameter-2 Moore graphs, and the degree-57 cell is still open ([Wikipedia: Moore graph](https://en.wikipedia.org/wiki/Moore_graph)); Brouwer's tables list strongly regular graph parameters with their existence status ([Brouwer](https://aeb.win.tue.nl/graphs/srg/srgtab.html)).
- See also: T1322, T81, T1338
