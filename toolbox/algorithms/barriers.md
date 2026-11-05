# Barriers
Results that prove a class of methods cannot reach a target: relativization, natural proofs, algebrization, locality, extension complexity, integrality gaps, rigidity.

### T1011 Prove the approach cannot work
`prove` `bound` · stage: judge · signals: barrier
aka: barrier analysis, obstruction to a method, a model that satisfies every input of the method, name the barrier then step outside it, method class is blind, parity problem in sieve theory, Selberg's parity barrier, Friedlander–Iwaniec, approach keeps almost working
- What: exhibits a model that satisfies every input your method uses but violates the conclusion; then pick a method with a property that class lacks.
- Fits when: an approach keeps almost working, or many strong people failed the same way.
- Lean: —
- Example: sieve axioms cannot tell primes from numbers with an even number of prime factors ([Tao: parity problem](https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/); [Tricki: prove your approach cannot work](https://www.tricki.org/article/If_you_are_getting_stuck_then_try_to_prove_rigorously_that_your_approach_cannot_work)); Friedlander–Iwaniec's parity-sensitive sieve gives primes a² + b⁴ ([Wikipedia: Parity problem](https://en.wikipedia.org/wiki/Parity_problem_(sieve_theory))).
- See also: T1012, T1013, T1014, T1021, T1369

### T1012 Relativization
`prove` · stage: judge · signals: computation, barrier, resource-bound
aka: oracles, Baker–Gill–Solovay, relativizing proofs, simulation, diagonalization, P vs NP, IP = PSPACE does not relativize
- What: any technique that works relative to every oracle cannot settle P vs NP.
- Fits when: checking whether a planned argument is pure simulation or diagonalization.
- Lean: —
- Example: Baker–Gill–Solovay oracles ([Wikipedia: P versus NP problem](https://en.wikipedia.org/wiki/P_versus_NP_problem)); IP = PSPACE fails relative to a random oracle, so its proof does not relativize ([Wikipedia: Relativization](https://en.wikipedia.org/wiki/Relativization)).
- See also: T1014, T1011

### T1013 Natural proofs
`prove` · stage: judge · signals: computation, barrier, resource-bound
aka: Razborov–Rudich, constructivity, largeness, usefulness, pseudorandom functions, PRFs, P/poly, circuit lower bounds
- What: constructive, large and useful properties cannot separate P/poly from NP if strong pseudorandom functions exist.
- Fits when: judging a circuit-lower-bound plan built on a simple, common property.
- Lean: —
- Example: Razborov–Rudich ([Wikipedia: Natural proof](https://en.wikipedia.org/wiki/Natural_proof)).
- See also: T1041, T1040

### T1014 Algebrization
`prove` · stage: judge · signals: computation, polynomial, barrier, resource-bound
aka: Aaronson–Wigderson, arithmetization, algebraic oracles, low-degree extensions, IP = PSPACE-style simulation
- What: arithmetization alone cannot settle P vs NP.
- Fits when: plans built on IP = PSPACE-style algebraic simulation.
- Lean: —
- Example: Aaronson–Wigderson ([ECCC TR08-005](https://eccc.weizmann.ac.il/report/2008/005/); [Wikipedia: P versus NP problem](https://en.wikipedia.org/wiki/P_versus_NP_problem)); arithmetization beats relativization but not algebrization (same ECCC report).
- See also: T1048, T1012

### T1015 Hardness magnification and the locality barrier
`prove` `bound` · stage: judge · signals: computation, barrier, resource-bound
aka: hardness magnification, weak lower bounds imply strong separations, locality barrier, oracle-augmented local circuits, how close a weak bound is to a breakthrough
- What: weak lower bounds for special problems imply strong separations; but arguments that also hold for local circuits with oracles cannot finish the job.
- Fits when: judging how close a weak bound is to a breakthrough; plans that combine weak lower bounds with magnification.
- Lean: —
- Example: [Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam](https://arxiv.org/abs/1911.08297).
- See also: T1042, T1013

### T1016 Extension complexity lower bounds
`bound` `prove` · stage: judge · signals: geometry, matrix, barrier, resource-bound
aka: extended formulations, extension complexity, slack matrix, nondeterministic communication, rectangle covers, compact LP formulation, TSP polytope, cut polytope, stable-set polytope
- What: rectangle covers of a polytope's slack matrix (nondeterministic communication) lower-bound the size of any LP that projects to the polytope.
- Fits when: before trying to prove a bound with a compact LP formulation.
- Lean: —
- Example: no polynomial-size LP projects to the TSP, cut or stable-set polytope ([Fiorini et al.](https://arxiv.org/abs/1111.0837)).
- See also: T48, T1032, T1037

### T1017 Integrality gaps and SoS lower bounds
`bound` · stage: judge · signals: graph, random, barrier, resource-bound
aka: integrality gap, sum-of-squares lower bounds, SoS degree, Lasserre, planted clique, G(n,1/2), relaxation cannot certify, clique-type bounds on random-like objects
- What: relaxations of bounded degree provably cannot certify the truth.
- Fits when: before spending compute on higher-degree SoS or SDP for clique-type bounds on random-like objects.
- Lean: —
- Example: the degree-d SoS value for clique on G(n,1/2) is about n^{1/2} ([Barak et al.](https://arxiv.org/abs/1604.03084)).
- See also: T54, T56, T1071

### T1018 Rigidity refutation
`prove` · stage: judge · signals: matrix, barrier, resource-bound
aka: matrix rigidity, probabilistic rank, Valiant's program, Walsh–Hadamard matrix, low rank after few changes, rigidity barrier
- What: shows that a candidate matrix family has low rank after few entry changes, which rules out a lower-bound route that needs it to be rigid.
- Fits when: a matrix-based lower-bound plan needs a specific matrix to be rigid.
- Lean: —
- Example: the Walsh–Hadamard matrix is not rigid enough for Valiant's program ([Alman–Williams](https://arxiv.org/abs/1611.05558)).
- See also: T1046
