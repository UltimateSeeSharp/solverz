# Quantum methods
Quantum detours for classical statements, bounds on quantum strategies, nonlocal games as reductions, and codes from group complexes.

### T1049 Quantum arguments for classical theorems
`prove` · stage: reformulate · signals: quantum, matrix, set-family
aka: quantum detour, quantum information inequalities, locally decodable codes, matrix questions, quantum proofs of classical results
- What: proves a classical statement through a quantum detour.
- Fits when: matrix, locally-decodable-code or lower-bound questions where quantum information gives a slick inequality.
- Lean: —
- Example: a survey of such results and the tools ([Drucker–de Wolf](https://arxiv.org/abs/0910.3376)).
- See also: T1029

### T1050 NPA hierarchy for quantum correlations
`bound` · stage: relax · signals: quantum, game, inequality
aka: Navascués–Pironio–Acín, nonlocal games, Bell inequalities, Bell expressions, Tsirelson's bound, CHSH, 2√2, noncommutative polynomial optimization, entangled value, operator-valued solutions
- What: a convergent hierarchy of SDPs bounds the value of a nonlocal game or Bell expression over all quantum strategies.
- Fits when: bounding an optimum over operator-valued (noncommutative) solutions.
- Lean: the dual SDP solution rounded to rationals (T124) and checked as in T53.
- Example: Navascués–Pironio–Acín ([arXiv:quant-ph/0607119](https://arxiv.org/abs/quant-ph/0607119)); Tsirelson's 2√2 bound for CHSH ([Wikipedia: Tsirelson's bound](https://en.wikipedia.org/wiki/Tsirelson%27s_bound)).
- See also: T53, T54, T56, T1051

### T1051 Nonlocal games as a reduction target
`prove` · stage: argue · signals: quantum, operator, game, computation
aka: MIP* = RE, entangled games, entangled value, rigidity, self-testing, compression, Tsirelson's problem, Connes' embedding conjecture, operator algebras, undecidability
- What: encodes a computation or an algebraic property in the entangled value of a game; rigidity (self-testing) and compression make the reduction work.
- Fits when: an operator-algebra or C*-algebra statement may be undecidable or false.
- Lean: —
- Example: MIP* = RE reduces the halting problem to entangled game values and refutes Tsirelson's problem and Connes' embedding conjecture ([arXiv:2001.04383](https://arxiv.org/abs/2001.04383); [Wikipedia: Connes embedding problem](https://en.wikipedia.org/wiki/Connes_embedding_problem)).
- See also: T1050, T1010

### T1052 Codes from group complexes
`find` · stage: construct · signals: group, set-family, quantum, construction
aka: lifted products, left–right Cayley complexes, expanding complexes, good quantum LDPC codes, locally testable codes, c³ locally testable codes, rate, distance, local testability
- What: builds expanding complexes from groups and reads classical or quantum codes off them.
- Fits when: codes or complexes with simultaneous rate, distance and local testability are wanted.
- Lean: —
- Example: Panteleev–Kalachev's good quantum LDPC codes ([arXiv:2111.03654](https://arxiv.org/abs/2111.03654)); Dinur–Evra–Livne–Lubotzky–Mozes's c³ locally testable codes ([arXiv:2111.04808](https://arxiv.org/abs/2111.04808)).
- See also: T1075, T1072
