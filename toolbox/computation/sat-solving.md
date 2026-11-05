# SAT solving and clausal proofs
SAT solvers on CNF encodings, and the UNSAT proofs (DRAT, LRAT, PR) that make their answers checkable.

### T1 CDCL SAT solving
`find` `prove` `bound` `compute` · stage: search · signals: local-constraints, colouring, construction, impossibility
aka: Kissat, CaDiCaL, PySAT, conflict-driven clause learning, CNF, incremental SAT, cardinality and pseudo-Boolean encodings, MaxSAT, MUS, Erdős discrepancy problem, ±1 sequences
- What: clause-learning search on CNF; PySAT adds incremental solving, cardinality and pseudo-Boolean encodings, and MaxSAT and MUS tools.
- Fits when: a finite existence or non-existence question with about 10^5–10^6 variables; optima by incremental bounds.
- Lean: a model by `decide +kernel`; UNSAT needs a kernel-checked LRAT (T5).
- Example: Erdős discrepancy for C=2: a ±1 sequence of length 1160 with discrepancy 2 exists, and none of length 1161 does ([Konev–Lisitsa](https://arxiv.org/abs/1402.2184); [Kissat](https://github.com/arminbiere/kissat); [PySAT](https://pysathq.github.io/)).
- See also: T2, T3, T4, T5, T119

### T2 Local-search SAT
`find` · stage: local-search · signals: local-constraints, colouring, construction
aka: WalkSAT, GSAT, probSAT, stochastic local search, noisy clause flips
- What: flips variables of unsatisfied clauses with noise; often finds satisfying assignments far faster than CDCL, but proves nothing for UNSAT.
- Fits when: large satisfiable find instances (colourings, designs).
- Lean: the assignment by `decide +kernel`; a failed run proves nothing.
- Example: GSAT and WalkSAT ([Wikipedia: WalkSAT](https://en.wikipedia.org/wiki/WalkSAT)).
- See also: T1, T90

### T3 Cube-and-conquer
`prove` `compute` · stage: search · signals: local-constraints, colouring, impossibility
aka: lookahead splitting, parallel SAT, cubes, Boolean Pythagorean triples problem, monochromatic a²+b²=c²
- What: a lookahead solver splits the problem into many cubes and CDCL solves each; embarrassingly parallel.
- Fits when: hard UNSAT instances where a single CDCL run stalls; it scales linearly with cores.
- Lean: a Lean lemma that the cubes cover all assignments, then one LRAT per cube (T5); kernel-only only when cubes are small.
- Example: Boolean Pythagorean triples: ℕ cannot be 2-coloured without a monochromatic a²+b²=c²; 800 cores for 2 days, a 200 TB DRAT proof compressed to a 68 GB certificate ([Heule–Kullmann–Marek](https://arxiv.org/abs/1605.00723)).
- See also: T1, T5, T122, T154

### T4 DRAT/LRAT proof logging
`prove` `compute` · stage: certify · signals: local-constraints, impossibility
aka: drat-trim, RUP, RAT, clausal proofs, UNSAT certificate, unsatisfiable core, proof trimming, Schur number five
- What: the solver logs each clause it adds; the checker validates RUP/RAT steps, trims and extracts cores; LRAT adds hints so checking is linear.
- Fits when: every UNSAT claim; trim before storing.
- Lean: Lean core's verified LRAT checker reads LRAT but reaches proofs only by native evaluation; kernel-only import is T5.
- Example: Schur number 5 is 160; the proof is about 2 PB and was certified by a formally verified checker ([Heule](https://arxiv.org/abs/1711.08076); [drat-trim](https://github.com/marijnheule/drat-trim)).
- See also: T5, T6, T123

### T5 Kernel-checked LRAT import
`prove` `compute` · stage: certify · signals: local-constraints, impossibility
aka: lrat-catcher, lrat_proof, streaming LRAT, resumable chunked import, Lean core LRAT checker, R(4,4)=18, Keller graph G(7,3), van der Waerden w(2;3,18), empty hexagon
- What: turns an LRAT refutation into a Lean theorem; lrat-catcher checks LRAT while the solver writes it, in resumable chunks, with cube-and-conquer support; its default mode adds one native axiom per import and does not count here.
- Fits when: an UNSAT result must count in Lean and its certificate is small.
- Lean: Mathlib `lrat_proof` (RUP only, out of memory at 63 MB) or lrat-catcher `+kernel` (full RAT, slower, embeds the CNF as a term; pins Lean v4.30.0, needs a port).
- Example: lrat-catcher imported R(4,4)=18 (85.5 GB) and Keller G(7,3) (773 GB) in native mode, plus w(2;3,18)=312 (25.9 TB) and a 174 TB re-import of the empty hexagon ([Szeider 2026](https://arxiv.org/abs/2607.00815); [lrat-catcher](https://github.com/leansolving/lrat-catcher)).
- See also: T3, T4, T120, T122, T127

### T6 Propagation-redundancy proofs
`prove` · stage: certify · signals: symmetric, impossibility
aka: PR, LPR, SR, substitution redundancy, cake_lpr, CakeML, dsr-trim, pigeonhole principle, Keller's conjecture
- What: PR steps give short proofs without new variables; LPR extends LRAT, and cake_lpr is a checker verified in CakeML.
- Fits when: symmetric, pigeonhole-like problems where RUP proofs explode.
- Lean: Trestle has a verified LSR checker (SR ⊇ PR) in Lean 4, but it pins Lean v4.21.0 and ran as compiled code; port it to the kernel, convert to LRAT, or avoid PR.
- Example: cake_lpr checks PR proofs directly, while converting them to weaker systems "greatly increased" size and checking time ([Tan–Heule–Myreen](https://research.chalmers.se/en/publication/531575)); the Lean 4 Keller proof checked its SR proofs with Trestle's LSR checker ([ITP 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.26)).
- See also: T4, T24, T25

### T7 SAT+CAS
`find` `prove` `compute` · stage: search · signals: set-family, finite-field, impossibility
aka: SAT plus computer algebra, orderly generation inside SAT, algebraic pruning, Lam's problem, projective plane of order 10, Kochen–Specker systems, orthogonality constraints, designs
- What: a computer algebra system supplies isomorph-free orderly generation or algebraic pruning to the SAT search.
- Fits when: objects with algebraic side conditions (orthogonality, designs).
- Lean: each CAS-made clause needs a Lean justification; out of reach at terabyte scale.
- Example: there is no projective plane of order 10, with nonexistence certificates; the work also found inconsistencies in earlier searches ([Bright et al.](https://arxiv.org/abs/2012.04715)); a 3-D Kochen–Specker system needs at least 24 vectors, with a 40.3 TiB certificate ([Li–Bright–Ganesh](https://arxiv.org/abs/2306.13319)).
- See also: T30, T31

### T8 Co-certificate learning
`find` `prove` · stage: search · signals: graph, colouring, impossibility
aka: CEGAR inside SMS, counterexample-guided abstraction refinement, ∃∀ problems, alternating problems, smallest triangle-free non-k-colourable graph, Kochen–Specker
- What: for "∃ object, ∀ witness fails" problems, each failing candidate's co-NP certificate becomes a learned clause.
- Fits when: alternating problems, such as the smallest triangle-free graph that is not k-colourable.
- Lean: the final UNSAT proof (T5) plus one Lean lemma per kind of learned clause.
- Example: improved the Kochen–Specker lower bound, orders of magnitude faster than earlier SAT methods ([Kirchweger–Peitl–Szeider](https://www.ijcai.org/proceedings/2023/0216.pdf)).
- See also: T9, T31, T110

### T9 QBF solving with certificates
`find` `prove` · stage: search · signals: game, logic
aka: quantified Boolean formulas, TQBF, ∃∀ formulas, PSPACE, sKizzo, Skolem-function certificates, finite two-player games, synthesis
- What: decides ∃∀ formulas as two-player games; some solvers extract Skolem-function certificates.
- Fits when: "there is an object such that every challenge fails", finite games, synthesis.
- Lean: —
- Example: QBF is the canonical PSPACE-complete problem; sKizzo extracts certificates ([Wikipedia: True quantified Boolean formula](https://en.wikipedia.org/wiki/True_quantified_Boolean_formula)).
- See also: T8, T110, T113

### T10 SAT on a reduced base case
`prove` · stage: encode · signals: impossibility
aka: automated impossibility theorems, social choice, mechanism design, voting rules, ranking sets of objects, lifting from small domains
- What: proves that an impossibility on small domains lifts to all domains, then SAT-checks the base case.
- Fits when: axiomatic impossibility results (social choice, mechanism design).
- Lean: the lifting lemma in Lean; the base case as a small UNSAT certificate (T5).
- Example: Geist–Endriss automate impossibility theorems for ranking sets of objects ([arXiv:1401.3866](https://arxiv.org/abs/1401.3866)).
- See also: T1, T119

### T11 Re-encoding historical exhaustive searches
`prove` `compute` · stage: encode · signals: geometry, impossibility
aka: legacy computer proofs, re-verification, Erdős–Szekeres, happy ending problem, convex hexagon, 17 points in general position
- What: replaces a bespoke enumeration with a modern encoding plus symmetry breaking.
- Fits when: old computer proofs that are slow or unverified.
- Lean: proofs this small may make kernel LRAT realistic (unverified: the source gives no certificate size).
- Example: the hexagon case of Erdős–Szekeres (17 points) went from over 3000 GHz-hours to about 1 GHz-hour, formalized in Isabelle/HOL ([Marić](https://research.matf.bg.ac.rs/handle/123456789/597)).
- See also: T1, T24, T119

### T12 Certified model counting (CPOG)
`compute` · stage: certify · signals: exact-value, local-constraints
aka: #SAT, model counting, knowledge compilation, partitioned-operation graph, weighted model counting, number of solutions
- What: compiles a CNF to a partitioned-operation graph with an equivalence proof, then counts from it.
- Fits when: compute problems that ask "how many".
- Lean: the checker is proved sound in Lean but runs as compiled code, so its counts do not count here; kernel use is untested, so plan only small counts.
- Example: the first formally verified toolchain for weighted and unweighted model counting, with its checker verified in Lean 4 ([Bryant–Nawrocki–Avigad–Heule](https://arxiv.org/abs/2501.12906)).
- See also: T38, T120
