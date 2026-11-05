# Deadlock breakers
What to try when every standard approach has failed; each entry names in "Fits when" the situation it answers.

### T1367 Move to a neighbour where a method works
`prove` `bound` · stage: reformulate
aka: nearby problem, variant, auxiliary problem, off-diagonal Ramsey, R(k, l), density increment, Campos et al., diagonal Ramsey
- What: solves a nearby problem that admits an increment or induction, then returns.
- Fits when: the direct problem has no handle, but a variant of it does.
- Lean: —
- Example: Campos et al. were stuck for years until passing to off-diagonal R(k, l) allowed a density increment ([Quanta](https://www.quantamagazine.org/after-nearly-a-century-a-new-limit-for-patterns-in-graphs-20230502/)).
- See also: T1313, T1371

### T1368 Accept a weaker tool that fits
`prove` `bound` · stage: practice
aka: lose efficiency to gain flexibility, sharp tool does not fit, less efficient sieve, numbers without large prime factors, Zhang, bounded prime gaps
- What: gives up efficiency for flexibility.
- Fits when: the sharp tool exists but does not fit the framework.
- Lean: —
- Example: Zhang's sieve on numbers without large prime factors ([Quanta](https://www.quantamagazine.org/yitang-zhang-proves-landmark-theorem-in-distribution-of-prime-numbers-20130519/)).
- See also: T1311, T1375

### T1369 Root-cause the failure
`prove` · stage: practice
aka: use the failure, five whys, root-cause analysis, why it fails, failed step, structural reason, obstruction, missing invariant, Wiles, Kolyvagin–Flach, Iwasawa theory
- What: asks why a step fails, then why that holds, until reaching a structural reason (an example, an obstruction, a missing invariant); the way a method fails can be the missing ingredient.
- Fits when: a nearly working argument fails at one identifiable point.
- Lean: —
- Example: [Wikipedia: Five whys](https://en.wikipedia.org/wiki/Five_whys); Wiles traced his gap to the Kolyvagin–Flach bound, and the reason it failed, with Iwasawa theory, became the fix on 19 September 1994 ([Wikipedia: Wiles's proof of Fermat's Last Theorem](https://en.wikipedia.org/wiki/Wiles%27s_proof_of_Fermat%27s_Last_Theorem)).
- See also: T1325, T1335

### T1370 Bet on the other truth value
`prove` `find` · stage: practice
aka: try the opposite, search for a counterexample, disprove, attack the negation, decades of failed proofs, Hirsch conjecture, Keller's conjecture, Kaplansky's unit conjecture, bunkbed conjecture, Kadison–Singer
- What: searches seriously for a counterexample, or for a proof if everyone expects a counterexample.
- Fits when: decades of failed proofs, or an "obvious" intuition with no mechanism behind it.
- Lean: —
- Example: Hirsch ([Wikipedia: Hirsch conjecture](https://en.wikipedia.org/wiki/Hirsch_conjecture)), Keller ([Wikipedia: Keller's conjecture](https://en.wikipedia.org/wiki/Keller%27s_conjecture)), unit ([arXiv:2102.11818](https://arxiv.org/abs/2102.11818)) and bunkbed ([arXiv:2410.02545](https://arxiv.org/abs/2410.02545)) fell to counterexamples; Kadison–Singer was expected false and was true ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)).
- See also: T1324, T1356

### T1371 Solve a richer model first
`find` `prove` · stage: reformulate · signals: construction
aka: gadgets with margin, robust gadgets, hypergraph first, weighted version, vector-valued version, simulate the extra features, Hollom, bunkbed counterexample, 7,222 vertices, Hilbert-space-valued sequences, Erdős discrepancy
- What: proves or builds a version in a richer model (hypergraph, weights, vector values), then simulates each extra feature by a robust gadget.
- Fits when: the plain model is too rigid to build in.
- Lean: —
- Example: Hollom's hypergraph counterexample to the bunkbed conjecture became a 7,222-vertex graph only after a robust version was built ([arXiv:2410.02545](https://arxiv.org/abs/2410.02545); [Quanta](https://quantamagazine.org/maths-bunkbed-conjecture-has-been-debunked-20241101/)); Tao's EDP proof covers Hilbert-space-valued sequences ([arXiv:1509.05363](https://arxiv.org/abs/1509.05363)).
- See also: T1367

### T1372 Tweak a near-miss
`find` `prove` `bound` · stage: practice · signals: near-miss
aka: change signs, change weights, change dimensions, almost-working construction, signed adjacency matrix, Huang, sensitivity conjecture, Maynard, GPY weights
- What: changes signs, weights or dimensions of an almost-working construction.
- Fits when: a classical tool or construction gives almost the bound.
- Lean: —
- Example: Huang's signed adjacency matrix ([arXiv:1907.00847](https://arxiv.org/abs/1907.00847)); Maynard's refined GPY weights ([arXiv:1311.4600](https://arxiv.org/abs/1311.4600)).
- See also: T1362

### T1373 Look for the exact certificate where numerics are tight
`bound` · stage: relax · signals: numeric-only, inequality
aka: tight LP bound, tight SDP bound, exact dual certificate, special-function family, modular forms, magic function, matching digits, sphere packing, Viazovska
- What: if an LP or SDP bound is numerically sharp, an exact certificate probably exists in a special-function family.
- Fits when: computed bounds match the best construction to many digits.
- Lean: an exact certificate is checkable; floating-point output is not (T124).
- Example: Viazovska's modular-form function ([Wikipedia: Sphere packing](https://en.wikipedia.org/wiki/Sphere_packing); [arXiv:1603.04246](https://arxiv.org/abs/1603.04246)).
- See also: T50, T53, T124, T1312

### T1374 Bring in an outsider or post openly
`find` `prove` `bound` `compute` · stage: practice
aka: outsiders, neighbouring field, ask a specialist, blog comment, Kalai, Spielman, Kadison–Singer, Uwe Stroinski, Tao, Erdős discrepancy problem
- What: a neighbouring field may already own the tool; ask outsiders, or post the problem openly.
- Fits when: insiders' tools are exhausted.
- Lean: —
- Example: Kalai pointed Spielman to Kadison–Singer ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)); a blog comment by Uwe Stroinski pointed Tao to EDP ([Quanta](https://www.quantamagazine.org/a-magical-answer-to-an-80-year-old-puzzle-20151001/)).
- See also: T1342, T1355

### T1375 Try elementary tools nobody tried
`prove` `bound` · stage: practice
aka: old simple theorem, outside the fashion, Cauchy interlacing, sensitivity conjecture, polynomial method, dimension counting, cap sets, Kakeya
- What: applies an old, simple theorem from outside the field's fashion.
- Fits when: decades of heavy machinery have failed.
- Lean: —
- Example: the 200-year-old Cauchy interlacing theorem ([Quanta](https://www.quantamagazine.org/mathematician-solves-computer-science-conjecture-in-two-pages-20190725/)); polynomial dimension counting for cap sets and Kakeya ([Wikipedia: Cap set](https://en.wikipedia.org/wiki/Cap_set); [Wikipedia: Kakeya set](https://en.wikipedia.org/wiki/Kakeya_set)).
- See also: T1339, T1368

### T1376 Step away and return
`find` `prove` `bound` `compute` · stage: practice
aka: incubation, Wallas, preparation, illumination, verification, long breaks, alternate problems, sleep, Huang, Gardam, Gilmer, union-closed conjecture
- What: Wallas' stages are preparation, incubation, illumination, verification; long breaks with low load help.
- Fits when: the same ideas recur without progress; switch to other work and return to the stuck problem later.
- Lean: —
- Example: [Wikipedia: Incubation (psychology)](https://en.wikipedia.org/wiki/Incubation_(psychology)); Huang came back to sensitivity after each paper for about seven years ([Quanta](https://www.quantamagazine.org/mathematician-solves-computer-science-conjecture-in-two-pages-20190725/)); Gardam returned after a year away ([Münster](https://www.uni-muenster.de/MathematicsMuenster/de/news/artikel/2021-03-04.shtml)); Gilmer returned to union-closed nine years after a failed year on it ([Quanta](https://www.quantamagazine.org/long-out-of-math-an-ai-programmer-cracks-a-pure-math-problem-20230103/)).
- See also: T1354
