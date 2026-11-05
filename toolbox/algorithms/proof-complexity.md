# Proof complexity
Predicts how large a certificate in a given proof system must be, which proof system a solver simulates, and how to certify parity reasoning.

### T1019 Size–width trade-off
`prove` `compute` · stage: judge · signals: local-constraints, impossibility, resource-bound
aka: resolution width, resolution size, Ben-Sasson–Wigderson, exponential resolution lower bounds, narrow proofs, predicting certificate size, clausal proofs
- What: short resolution proofs are narrow, so width lower bounds give size lower bounds.
- Fits when: predicting whether a SAT certificate can be small enough for the Lean kernel.
- Lean: — (it decides whether T5 can work)
- Example: simple proofs of exponential resolution lower bounds ([Ben-Sasson–Wigderson](https://eccc.weizmann.ac.il/report/1999/022/)).
- See also: T4, T5, T1020, T1021

### T1020 Know what your solver simulates
`prove` `compute` · stage: judge · signals: local-constraints, impossibility, resource-bound
aka: DPLL is tree-like resolution, CDCL and resolution, proof system of a solver, pigeonhole principle, Haken, cardinality reasoning, extension variables, symmetry breaking, formulas hard for solvers
- What: DPLL equals tree-like resolution and CDCL is at most resolution, so formulas hard for the proof system are hard for the solver.
- Fits when: before encoding; pigeonhole-like counting needs cardinality reasoning, extension variables or symmetry breaking.
- Lean: —
- Example: Haken's exponential resolution lower bound for the pigeonhole principle ([Wikipedia: Proof complexity](https://en.wikipedia.org/wiki/Proof_complexity)).
- See also: T1, T6, T24, T25

### T1021 Certificate-size barrier
`prove` `compute` · stage: judge · signals: graph, colouring, barrier, resource-bound
aka: proof-size lower bounds, Ramsey statements in resolution, no clique or independent set of size c·log n, n^{Ω(log n)}, brute force optimal for resolution, certificate too big for the kernel, 200 TB Pythagorean triples proof
- What: proof-complexity lower bounds cap what any certificate in a given proof system can achieve; resolution proofs that a graph has no clique or independent set of size c·log n need length n^{Ω(log n)}.
- Fits when: deciding whether a result can ever fit the Lean kernel in that format; for Ramsey-type non-existence brute force is essentially optimal for resolution, so use stronger reasoning (symmetry, counting).
- Lean: —
- Example: Ramsey-statement resolution lower bounds ([Lauria–Pudlák–Rödl–Thapen](https://arxiv.org/abs/1303.3166)); the 200 TB DRAT proof for Boolean Pythagorean triples ([Heule–Kullmann–Marek](https://arxiv.org/abs/1605.00723)).
- See also: T3, T5, T154, T1011

### T1022 Feasible interpolation
`prove` · stage: argue · signals: computation, resource-bound
aka: interpolation in proof systems, interpolants, short proofs give small circuits, cutting planes lower bounds, Pudlák, automatability
- What: short proofs of certain formulas yield small circuits that separate two sets, so circuit lower bounds become proof-size lower bounds.
- Fits when: lower bounds for proof systems; judging automatability.
- Lean: —
- Example: Pudlák's cutting-planes lower bounds via interpolation ([Wikipedia: Proof complexity](https://en.wikipedia.org/wiki/Proof_complexity)).
- See also: T1041

### T1023 Parity (XOR) certification
`prove` · stage: certify · signals: parity, local-constraints, impossibility
aka: Gaussian elimination proofs, XOR constraints, Tseitin formulas, extension variables, pseudo-Boolean proof logging, VeriPB, parity reasoning in SAT
- What: justifies Gaussian-elimination steps with extension variables in pseudo-Boolean proofs.
- Fits when: problems with parity structure (Tseitin-like), which are hard for plain resolution.
- Lean: needs a VeriPB checker in the kernel; pb-catcher runs by native evaluation and does not count (T25).
- Example: [Gocht–Nordström](https://arxiv.org/abs/2209.12185).
- See also: T4, T25
