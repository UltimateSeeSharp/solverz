# Constraint and SMT solving
Solvers beyond plain SAT: SMT, constraint programming, answer set programming and model checking.

### T13 SMT with Lean replay
`prove` `find` · stage: search · signals: integers, local-constraints, inequality
aka: Z3, cvc5, lean-smt, satisfiability modulo theories, linear integer and real arithmetic, uninterpreted functions, bitvectors, MILP certificate checking
- What: decides quantifier-free theories (linear integer and real arithmetic, uninterpreted functions, bitvectors).
- Fits when: goals that mix arithmetic and uninterpreted functions; side conditions of certificates.
- Lean: lean-smt (beta) replays cvc5 proofs as Lean terms; holes come back as goals and some reconstruction lemmas are silent `sorry`, so check `#print axioms` (T127); pins Lean v4.34.0, needs cvc5.
- Example: MILP (VIPR) certificates checked as one large arithmetic formula with cvc5; all 106 benchmark certificates were confirmed ([Verifying MILP certificates with SMT](https://ar5iv.labs.arxiv.org/html/2312.10420); [Z3](https://github.com/Z3Prover/z3); [lean-smt](https://github.com/ufmg-smite/lean-smt)).
- See also: T49, T129, T130

### T14 Constraint programming (CP-SAT)
`find` `compute` `bound` · stage: search · signals: local-constraints, construction
aka: OR-Tools CP-SAT, global constraints, all-different, scheduling, quasigroups, Latin squares, model generation, enumerate all solutions
- What: integer constraint programming with propagation and SAT-style learning; enumerates all solutions or optimizes.
- Fits when: global constraints (all-different, scheduling-like structure) and quick feasibility probes.
- Lean: solutions by `decide +kernel`; infeasibility needs proof logging (T25) or a SAT re-encoding (T5).
- Example: open existence questions for quasigroups settled by model-generation search ([Fujita–Slaney–Bennett 1993](https://mlanthology.org/ijcai/1993/fujita1993ijcai-automatic/); [CP-SAT](https://developers.google.com/optimization/cp/cp_solver)).
- See also: T1, T15, T19

### T15 Answer set programming
`find` `compute` · stage: encode · signals: local-constraints, construction
aka: ASP, clingo, clasp, gringo, Potassco, stable models, generate-and-test, declarative search encodings
- What: declarative generate-and-test search under stable-model semantics; compact encodings of combinatorial problems.
- Fits when: rapid prototyping of search encodings with recursion or defaults.
- Lean: an answer is a witness (T118); no Lean route for non-existence in the sources.
- Example: the Potassco tools clasp, gringo and clingo ([Wikipedia: Answer set programming](https://en.wikipedia.org/wiki/Answer_set_programming)).
- See also: T1, T14

### T16 Model checking
`prove` `find` · stage: decide · signals: dynamics, computation, impossibility
aka: bounded model checking, BMC, CEGAR, abstraction refinement, transition systems, temporal properties, reachability, safety, cellular automata, busy-beaver deciders
- What: explores the states of a transition system for a temporal property; bounded model checking unrolls into SAT; CEGAR refines abstractions from spurious counterexamples.
- Fits when: a process, game or machine must never reach a bad state (busy-beaver-style deciders, cellular automata).
- Lean: —
- Example: [Wikipedia: Model checking](https://en.wikipedia.org/wiki/Model_checking).
- See also: T1, T37, T112
