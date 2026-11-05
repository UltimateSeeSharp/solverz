# Research practice and philosophy of proof
How conjectures, proofs and research lines evolve, and what counts as evidence, understanding and progress.

### T1335 Proofs and refutations
`prove` · stage: practice
aka: Lakatos, guilty lemma, hidden lemma, monster-barring, monster-adjustment, proof-generated concepts, counterexample analysis, Euler polyhedron formula
- What: conjecture, rough proof, counterexample, find the guilty lemma, build it into the conjecture; monster-barring and monster-adjustment are the lazy alternatives.
- Fits when: a counterexample hits a conjecture or a proof sketch; it points to a hidden lemma, and the concept the proof generates becomes the new definition.
- Lean: —
- Example: the Euler polyhedron dialogues ([Wikipedia: Proofs and Refutations](https://en.wikipedia.org/wiki/Proofs_and_Refutations); [Wikipedia: Imre Lakatos](https://en.wikipedia.org/wiki/Imre_Lakatos)).
- See also: T1336, T1369

### T1336 Progressive and degenerating programmes
`find` `prove` `bound` `compute` · stage: practice
aka: Lakatos research programmes, novel predictions, ad hoc patches, absorbing anomalies, line health, retire a line
- What: a line is healthy while its adjustments predict new facts; patches that only absorb anomalies signal decay.
- Fits when: judging an idea line: did its last steps produce new facts? Retire degenerating lines once a replacement exists.
- Lean: —
- Example: [Wikipedia: Imre Lakatos](https://en.wikipedia.org/wiki/Imre_Lakatos).
- See also: T1337, T1354

### T1337 Anomalies and paradigm shifts
`find` `prove` `bound` `compute` · stage: practice
aka: Kuhn, normal science, puzzle solving, anomaly log, paradigm shift, new framework, The Structure of Scientific Revolutions
- What: normal science solves puzzles inside a framework until anomalies accumulate; then a new framework asks new questions of old data.
- Fits when: a line keeps collecting counterexamples and patches; record the anomalies explicitly and ask which framework would make them natural.
- Lean: —
- Example: [Wikipedia: The Structure of Scientific Revolutions](https://en.wikipedia.org/wiki/The_Structure_of_Scientific_Revolutions).
- See also: T1336, T1340

### T1338 Risky predictions
`find` `prove` `bound` `compute` · stage: practice
aka: Popper, falsifiability, corroboration, kill test, sharp conjecture, what a claim prohibits
- What: a claim is valuable by what it prohibits; prefer conjectures and intermediate claims that a cheap test could refute.
- Fits when: stating claims and kill tests; choosing between a vague and a sharp conjecture.
- Lean: —
- Example: falsifiability and corroboration of risky predictions ([Wikipedia: Falsifiability](https://en.wikipedia.org/wiki/Falsifiability)).
- See also: T136, T1334

### T1339 Few tricks
`find` `prove` `bound` `compute` · stage: practice
aka: Rota, "Even Hilbert had only a few tricks", catalogue of tricks, standard moves, apply known methods first
- What: each area has a few tricks; catalogue them and apply them systematically before inventing.
- Fits when: a new problem, before inventing a method.
- Lean: —
- Example: "Even Hilbert had only a few tricks!" ([Rota, lesson 5](https://heibeck.freeshell.org/Grad_Advice/Ten_Lessons.html)).
- See also: T1348

### T1340 Rising sea
`prove` · stage: practice
aka: Grothendieck, rising sea vs hammer and chisel, general theory, build the framework, the problem dissolves, étale cohomology, Weil conjectures
- What: builds general theory until the problem dissolves, instead of repeated direct strikes.
- Fits when: direct attacks keep failing; build the framework in which the statement is natural.
- Lean: —
- Example: [nLab: The Rising Sea](https://ncatlab.org/nlab/show/The+Rising+Sea); étale cohomology, developed by Grothendieck and Artin for attacking the Weil conjectures ([Wikipedia: Weil conjectures](https://en.wikipedia.org/wiki/Weil_conjectures)).
- See also: T1337

### T1341 Partial progress and reductions
`find` `prove` `bound` `compute` · stage: practice
aka: special cases, weaker bounds, reductions, partial results, record progress, outsiders finish, Kadison–Singer, Marcus
- What: records special cases, weaker bounds and reductions; each reduction narrows what remains.
- Fits when: the main problem stays open; outsiders often finish what insiders reduced.
- Lean: —
- Example: Tao, "On the importance of partial progress" ([Tao career advice](https://terrytao.wordpress.com/career-advice/)); Marcus: earlier work had removed most of the difficulty, leaving one piece specialists lacked tools for ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)).
- See also: T1355, T1374

### T1342 Literature archaeology
`prove` · stage: practice
aka: old papers, distant fields, the missing lemma already exists, exact inequality search, ask specialists, Askey–Gasper, de Branges, Rankin's trick, Deligne
- What: the missing lemma may exist in an old or distant paper.
- Fits when: a proof needs one specific inequality or identity; search for exactly it and ask specialists of neighbouring fields.
- Lean: —
- Example: Askey–Gasper (1976) had already proved de Branges's needed inequality ([Wikipedia: De Branges's theorem](https://en.wikipedia.org/wiki/De_Branges%27s_theorem)); Deligne used Rankin's 1939 trick ([Wikipedia: Weil conjectures](https://en.wikipedia.org/wiki/Weil_conjectures)).
- See also: T147, T1374

### T1343 Seek more proofs of known results
`prove` · stage: practice
aka: new proofs, alternative proofs, re-prove, Book proofs, Proofs from THE BOOK, Erdős, quadratic reciprocity, Gauss
- What: re-proves a theorem by unrelated methods; each new proof is a new tool, and short "Book" proofs reveal mechanisms.
- Fits when: a needed special case is known by only one heavy proof; preparing a method for an open neighbour.
- Lean: —
- Example: Gauss published six proofs of quadratic reciprocity; there are over 240 ([Wikipedia: Quadratic reciprocity](https://en.wikipedia.org/wiki/Quadratic_reciprocity)); Erdős's "Book" of best proofs ([Wikipedia: Proofs from THE BOOK](https://en.wikipedia.org/wiki/Proofs_from_THE_BOOK)).
- See also: T1375

### T1344 Understanding is progress
`find` `prove` `bound` `compute` · stage: practice
aka: Thurston, On proof and progress in mathematics, record why it works, mechanism, insight, after Lean accepts
- What: progress includes understanding that formal proofs do not capture.
- Fits when: Lean has accepted a result; record why it works, since understanding seeds the next problem.
- Lean: —
- Example: Thurston, "On proof and progress in mathematics" ([arXiv:math/9404236](https://arxiv.org/abs/math/9404236)).
- See also: T1345

### T1345 Label speculation
`find` `prove` `bound` `compute` · stage: practice
aka: Jaffe–Quinn, theoretical mathematics, speculative vs proved, heuristic vs theorem, status labels, credit both
- What: separates theoretical (speculative) work from proved work in writing, and credits both.
- Fits when: writing `understanding.md` or a report that mixes heuristics and theorems.
- Lean: —
- Example: Jaffe–Quinn, "Theoretical mathematics" ([arXiv:math/9307227](https://arxiv.org/abs/math/9307227)); Thurston's reply is T1344.
- See also: T1344, T1346

### T1346 Know what counts as proof
`find` `prove` `bound` `compute` · stage: practice
aka: status of evidence, sampled vs rigorous, computer-assisted proof, formal proof, high-confidence sampling, 99% certain, bunkbed conjecture, Kepler conjecture, Flyspeck
- What: sampled, computer-assisted and formal evidence differ in status.
- Fits when: a result rests on sampling or an unchecked computation; aim for a Lean-checkable certificate, and turn sampled evidence into a rigorous construction.
- Lean: here only a kernel check with standard axioms counts (T127).
- Example: Pak's team stopped at high-confidence sampling, then found a rigorous counterexample ([Quanta](https://quantamagazine.org/maths-bunkbed-conjecture-has-been-debunked-20241101/)); Kepler referees were "99% certain" until Flyspeck ([Wikipedia: Kepler conjecture](https://en.wikipedia.org/wiki/Kepler_conjecture)).
- See also: T127, T1331, T1345
