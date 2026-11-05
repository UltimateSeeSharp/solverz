# Sieve methods
Upper and lower bounds for sifted sets: combinatorial and Λ² sieves, multidimensional weights, the parity barrier and how to break it, large sieves, and covering congruences.

### T505 Brun's combinatorial sieve
`bound` · stage: argue · signals: integers, inequality
aka: Brun sieve, truncated inclusion–exclusion, Bonferroni inequalities, twin primes, prime k-tuples, Brun's constant, sifted sets
- What: truncates inclusion–exclusion with controlled error to bound sifted sets from above (and sometimes below).
- Fits when: upper bounds for twin primes and prime k-tuples.
- Lean: —
- Example: Brun's theorem: Σ 1/p over twin primes converges ([Wikipedia: Brun sieve](https://en.wikipedia.org/wiki/Brun_sieve)).
- See also: T338, T506

### T506 Selberg's Λ² sieve
`bound` · stage: argue · signals: integers, inequality
aka: Selberg sieve, Lambda-squared weights, quadratic form in sieve weights, upper bound sieve, Brun–Titchmarsh, level of distribution
- What: optimizes a quadratic form in the sieve weights; upper bounds within a constant of the truth.
- Fits when: upper bounds for sifted sets with a good level of distribution.
- Lean: Mathlib `SelbergSieve` (NumberTheory/SelbergSieve.lean): `upperMoebius_lambdaSquared` and `siftedSum_le_mainSum_errSum_of_upperMoebius`.
- Example: Brun–Titchmarsh-type bounds ([Wikipedia: Selberg sieve](https://en.wikipedia.org/wiki/Selberg_sieve)).
- See also: T505, T507, T489

### T507 Multidimensional sieve weights (GPY–Maynard)
`prove` · stage: argue · signals: integers, additive
aka: Goldston–Pintz–Yıldırım, Maynard–Tao sieve, bounded gaps between primes, admissible tuples, Zhang's theorem, Polymath8
- What: chooses weights over k-tuples so the expected number of primes among n + h_i exceeds 1.
- Fits when: showing several primes occur in admissible tuples.
- Lean: —
- Example: Maynard's bounded gaps between primes, building on Zhang ([arXiv:1311.4600](https://arxiv.org/abs/1311.4600), [Wikipedia: Yitang Zhang](https://en.wikipedia.org/wiki/Yitang_Zhang)).
- See also: T506, T489

### T508 Switching (Chen's trick)
`prove` `bound` · stage: argue · signals: integers, barrier
aka: Chen's theorem, switching principle, almost primes, P_2, p + P_2, parity barrier, lower bound by upper-bounding a complement
- What: lower-bounds one sifted set by upper-bounding a complementary one.
- Fits when: almost-prime results at the parity barrier.
- Lean: —
- Example: Chen's theorem: every large even number is p + P_2 ([Wikipedia: Chen's theorem](https://en.wikipedia.org/wiki/Chen's_theorem)).
- See also: T509, T506, T1011

### T509 Breaking parity with bilinear (Type II) input
`prove` · stage: argue · signals: integers, barrier, parity
aka: parity problem, Type II sums, bilinear forms, Friedlander–Iwaniec, primes of the form a² + b⁴, thin polynomial sequences
- What: injects non-sieve bilinear estimates to tell odd from even numbers of prime factors.
- Fits when: prime-producing results on thin polynomial sequences.
- Lean: —
- Example: Friedlander–Iwaniec: infinitely many primes of the form a² + b⁴ ([Wikipedia: Friedlander–Iwaniec theorem](https://en.wikipedia.org/wiki/Friedlander–Iwaniec_theorem), [Wikipedia: Parity problem](https://en.wikipedia.org/wiki/Parity_problem_%28sieve_theory%29)).
- See also: T485, T508, T1011

### T510 Large and larger sieves
`bound` · stage: argue · signals: integers, congruence, inequality
aka: large sieve, Gallagher's larger sieve, Linnik, least quadratic non-residue on average, many removed residue classes, missing digits, sets missing classes mod prime powers
- What: sieves out many residue classes mod each prime; Gallagher's larger sieve handles sets missing classes mod prime powers.
- Fits when: very many removed classes (quadratic non-residues, missing digits).
- Lean: —
- Example: Linnik's large sieve for least quadratic non-residues on average; Gallagher's larger sieve ([Wikipedia: Large sieve](https://en.wikipedia.org/wiki/Large_sieve), [Wikipedia: Larger sieve](https://en.wikipedia.org/wiki/Larger_sieve)).
- See also: T488, T487

### T511 Covering congruences
`prove` `find` · stage: construct · signals: integers, congruence, construction
aka: covering systems, covering sets, Sierpiński numbers, k·2^n + 1 composite for all n, fixed prime factors, every member composite
- What: covers Z by finitely many residue classes so each member of a family has a fixed small prime factor.
- Fits when: proving every member of an infinite family is composite.
- Lean: that the classes cover Z/lcm, and each divisibility k·2^n + 1 ≡ 0 mod p on its class, by `decide +kernel`.
- Example: Sierpiński numbers such as 78557 (k·2^n + 1 composite for all n) via covering sets ([Wikipedia: Sierpiński number](https://en.wikipedia.org/wiki/Sierpiński_number), [Wikipedia: Covering system](https://en.wikipedia.org/wiki/Covering_system)).
- See also: T504, T118, T121
