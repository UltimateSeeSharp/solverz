# Circuit and algebraic complexity
Lower bounds for Boolean and algebraic circuits, the matrix-multiplication exponent, and arithmetization.

### T1040 Random restrictions and the switching lemma
`bound` · stage: argue · signals: computation, set-family, random, resource-bound
aka: Håstad's switching lemma, random restrictions, AC0, parity not in AC0, DNF to shallow decision tree, Fourier concentration of shallow circuits
- What: random partial assignments collapse DNFs to shallow decision trees.
- Fits when: AC0-type lower bounds, Fourier concentration of shallow circuits, structure under restrictions.
- Lean: —
- Example: Håstad: parity needs size exp(Ω(n^{1/(d−1)})) in depth d ([Wikipedia: Switching lemma](https://en.wikipedia.org/wiki/Switching_lemma)).
- See also: T1053, T1013

### T1041 Method of approximations
`bound` · stage: argue · signals: computation, graph, set-family, resource-bound
aka: Razborov's method, monotone circuits, monotone clique lower bound, Alon–Boppana, approximators, sunflowers, counting errors
- What: approximates each gate by a simple family and counts the errors.
- Fits when: monotone lower bounds; sunflower-type combinatorics feed the counting.
- Lean: —
- Example: Razborov's monotone clique lower bound, made exponential by Alon–Boppana ([Wikipedia: Circuit complexity](https://en.wikipedia.org/wiki/Circuit_complexity)).
- See also: T1036, T1022

### T1042 Gate elimination
`bound` · stage: argue · signals: computation, resource-bound
aka: explicit circuit lower bounds, substitution, linear lower bounds, affine dispersers, minimal circuits, exact circuit size
- What: substitutes variables to remove several gates per step.
- Fits when: explicit linear lower bounds for circuit size; also exact minimal-circuit problems.
- Lean: —
- Example: a (3+1/86)n lower bound for an affine disperser ([Find–Golovnev–Hirsch–Kulikov](https://eccc.weizmann.ac.il/report/2015/166/)).
- See also: T36, T1015

### T1043 Shannon counting
`prove` `bound` · stage: argue · signals: computation, asymptotic, resource-bound
aka: counting argument, most functions are hard, Θ(2^n/n) gates, existence of hard functions, random beats explicit
- What: there are too few small circuits to compute most functions.
- Fits when: existence of hard objects; the baseline for "random beats explicit".
- Lean: —
- Example: almost all n-input functions need Θ(2^n/n) gates ([Wikipedia: Circuit complexity](https://en.wikipedia.org/wiki/Circuit_complexity)).
- See also: T1013

### T1044 Algorithms to lower bounds
`prove` · stage: reformulate · signals: computation, resource-bound
aka: Williams' program, faster SAT algorithms imply lower bounds, circuit satisfiability, NEXP ⊄ ACC0, ACC0
- What: a slightly faster SAT algorithm for a circuit class C implies a lower bound against C.
- Fits when: algorithmic speedups are easier than direct lower bounds.
- Lean: —
- Example: Williams: NEXP ⊄ ACC0 ([Wikipedia: ACC0](https://en.wikipedia.org/wiki/ACC0)).
- See also: T1122

### T1045 Razborov–Smolensky polynomial approximation
`bound` · stage: argue · signals: polynomial, finite-field, computation, resource-bound
aka: AC0[p], modular circuits, low-degree approximation over F_p, probabilistic polynomials, MOD_m, ACC0
- What: approximates AC0[p] circuits by low-degree polynomials over F_p.
- Fits when: lower bounds against modular circuits; also an algorithmic tool.
- Lean: —
- Example: MOD_m ∉ AC0[p] unless m is a power of p ([Wikipedia: ACC0](https://en.wikipedia.org/wiki/ACC0)).
- See also: T1122

### T1046 Partial derivatives and set-multilinearization
`bound` · stage: argue · signals: polynomial, matrix, resource-bound
aka: algebraic circuit lower bounds, partial derivative method, rank of a derivative matrix, constant-depth algebraic circuits, iterated matrix multiplication, permanent-like polynomials, Limaye–Srinivasan–Tavenas
- What: measures a polynomial by the rank of a matrix of its partial derivatives, and shows that small circuits have low rank.
- Fits when: lower bounds for permanent-like or iterated matrix-product polynomials.
- Lean: —
- Example: Limaye–Srinivasan–Tavenas: superpolynomial lower bounds against constant-depth algebraic circuits ([ECCC TR21-081](https://eccc.weizmann.ac.il/report/2021/081/)).
- See also: T1018

### T1047 Laser method for ω
`bound` · stage: argue · signals: matrix, product-structure, asymptotic, resource-bound
aka: matrix multiplication exponent, ω, Coppersmith–Winograd tensor, tensor powers, value of a tensor, asymptotic tensor rank, Alman–Vassilevska Williams
- What: bounds the value of a tensor (a power of the Coppersmith–Winograd tensor) to bound the matrix-multiplication exponent.
- Fits when: asymptotic tensor-rank bounds, as opposed to finite schemes (T92, T104).
- Lean: —
- Example: Alman–Vassilevska Williams's refined laser method ([arXiv:2010.05846](https://arxiv.org/abs/2010.05846)).
- See also: T92, T104

### T1048 Arithmetization
`prove` · stage: reformulate · signals: polynomial, computation
aka: low-degree extensions, sum-check protocol, Boolean formulas as polynomials, interactive proofs, IP = PSPACE, Lund–Fortnow–Karloff–Nisan, Shamir, low-degree tests
- What: replaces Boolean formulas by low-degree polynomials over a field so that algebraic tools (sum-check, low-degree tests) apply.
- Fits when: interactive or probabilistic verification; algebraic lower and upper bounds.
- Lean: —
- Example: IP = PSPACE (Lund–Fortnow–Karloff–Nisan, Shamir) ([Wikipedia: IP (complexity)](https://en.wikipedia.org/wiki/IP_%28complexity%29)).
- See also: T1014, T1084
