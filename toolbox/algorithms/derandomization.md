# Derandomization and constructive existence
Turns random constructions into deterministic ones, judges when that is possible, and counts partial solutions to prove existence.

### T1062 Method of conditional expectations
`find` `bound` · stage: construct · signals: random, construction
aka: method of conditional probabilities, pessimistic estimators, derandomizing the probabilistic method, deterministic Max-Cut half cut, Turán-type independent sets, greedy derandomization
- What: fixes random choices one by one, keeping the conditional failure probability (or a pessimistic estimator of it) below 1.
- Fits when: a probabilistic existence proof should become a deterministic construction; the output is a concrete object Lean can check.
- Lean: the constructed object by `decide`.
- Example: a deterministic cut containing at least half the edges for Max-Cut; Turán-type independent sets ([Wikipedia: Method of conditional probabilities](https://en.wikipedia.org/wiki/Method_of_conditional_probabilities)).
- See also: T1063, T1076

### T1063 k-wise independence and small-bias spaces
`find` · stage: construct · signals: random, pseudorandom
aka: k-wise independent sample spaces, pairwise independence, small-bias spaces, ε-biased sets, small sample spaces, fooling low-degree tests, exhaustible families
- What: small sample spaces that fool low-degree tests.
- Fits when: shrinking a random construction to a polynomial-size family that can be searched exhaustively.
- Lean: each member of the family is a candidate checked by `decide`.
- Example: basic derandomization techniques, Vadhan ch. 3 ([Vadhan, Pseudorandomness](https://people.seas.harvard.edu/~salil/pseudorandomness/)).
- See also: T1062, T1057

### T1064 Hardness versus randomness
`prove` · stage: judge · signals: computation, pseudorandom, resource-bound
aka: Nisan–Wigderson, Impagliazzo–Wigderson, pseudorandom generators, PRG, BPP = P, derandomization in principle, hard functions
- What: hard functions yield pseudorandom generators that derandomize BPP.
- Fits when: judging whether a randomized method can be made deterministic in principle.
- Lean: —
- Example: PRG constructions, Vadhan ch. 7 ([Vadhan](https://people.seas.harvard.edu/~salil/pseudorandomness/)).
- See also: T1065, T1013

### T1065 Identity testing and circuit lower bounds
`prove` · stage: judge · signals: polynomial, computation, resource-bound
aka: polynomial identity testing, PIT, deterministic PIT, Kabanets–Impagliazzo, derandomizing identity testing forces lower bounds
- What: derandomizing polynomial identity testing forces circuit lower bounds.
- Fits when: judging a plan that needs deterministic identity testing.
- Lean: —
- Example: [Kabanets–Impagliazzo](https://eccc.weizmann.ac.il/report/2002/055/).
- See also: T126, T1066

### T1066 Derandomizing a specific identity test
`prove` · stage: argue · signals: polynomial, integers, congruence
aka: AKS primality test, PRIMES in P, (X+a)ⁿ ≡ Xⁿ+a, structured congruence, deterministic primality, replace random evaluation
- What: replaces a random evaluation by a structured congruence.
- Fits when: a randomized test whose polynomial has algebraic structure.
- Lean: to certify one prime, use Pratt certificates instead (T43).
- Example: AKS: (X+a)ⁿ ≡ Xⁿ+a mod (n, X^r−1) puts PRIMES in P ([Wikipedia: AKS primality test](https://en.wikipedia.org/wiki/AKS_primality_test)).
- See also: T43, T126, T1065

### T1067 Expander walks for derandomization
`prove` · stage: argue · signals: graph, computation
aka: SL = L, Reingold, undirected connectivity in logspace, derandomized random walks, space-bounded exploration, zig-zag product
- What: replaces a random walk by a walk on a derandomized expander.
- Fits when: space-bounded or exploration problems.
- Lean: —
- Example: SL = L ([Reingold](https://eccc.weizmann.ac.il/report/2004/094/)).
- See also: T1072

### T1068 Rosenfeld's counting method
`prove` `bound` · stage: argue · signals: colouring, graph, sequence
aka: counting partial solutions, inductive counting, alternative to entropy compression, nonrepetitive colourings, acyclic colourings, list colourings, bounded-degree graphs, Thue choice number
- What: counts partial solutions inductively and shows their number grows, so a full solution exists; simpler than entropy compression.
- Fits when: problems solved by entropy compression (nonrepetitive, acyclic and list colourings), with shorter, more formalizable proofs.
- Lean: —
- Example: improved nonrepetitive colouring bounds for bounded-degree graphs ([Rosenfeld](https://arxiv.org/abs/2006.09094)).
- See also: T1069

### T1069 Resampling oracles
`find` `prove` · stage: argue · signals: order, random, local-constraints
aka: algorithmic local lemma in non-product spaces, Harvey–Vondrák, Lovász local lemma, bad events, permutations, perfect matchings
- What: an algorithmic local lemma for non-product spaces such as permutations and perfect matchings.
- Fits when: bad events over permutations or perfect matchings.
- Lean: the found object by `decide`.
- Example: [Harvey–Vondrák](https://arxiv.org/abs/1504.02044).
- See also: T1068

### T1070 Isolation lemma
`prove` `find` · stage: argue · signals: random, set-family
aka: Mulmuley–Vazirani–Vazirani, Valiant–Vazirani, unique minimum-weight solution, random weights, unique-solution instances, parallel matching
- What: random weights make the minimum-weight solution unique with probability at least 1 − n/N.
- Fits when: reducing to unique-solution instances; parallel matching.
- Lean: —
- Example: Mulmuley–Vazirani–Vazirani; Valiant–Vazirani ([Wikipedia: Isolation lemma](https://en.wikipedia.org/wiki/Isolation_lemma)).
- See also: T1115
