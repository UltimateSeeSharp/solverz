# Additive combinatorics
Patterns in dense and sparse sets of integers and groups: density and energy increments, Gowers norms, transference, sumset calculus, Freiman and Bogolyubov, almost periodicity, sifting, entropic sumsets, sum-product, Behrend, growth in groups.

### T412 Fourier density increment
`prove` `bound` · stage: argue · signals: additive, dense
aka: Roth's argument, density increment, large Fourier coefficient, 3-term arithmetic progressions, x + y = z, Roth's theorem
- What: a set without the pattern has a large Fourier coefficient, hence a denser subset on a structured piece; iterate.
- Fits when: linear patterns (3-APs, x + y = z) in dense sets.
- Lean: Mathlib proves Roth's theorem by the corners route (`roth_3ap_theorem`, `Combinatorics/Additive/Corner/Roth.lean`), not by Fourier increment.
- Example: Roth's theorem on 3-term progressions ([Wikipedia: Roth's theorem on arithmetic progressions](https://en.wikipedia.org/wiki/Roth's_theorem_on_arithmetic_progressions), [Tricki: convolutions and Fourier](https://www.tricki.org/article/If_your_problem_can_be_expressed_in_terms_of_convolutions_and_inner_products_then_take_the_Fourier_transform)).
- See also: T413, T420, T424, T346

### T413 Energy increment and the structure/randomness dichotomy
`prove` · stage: argue · signals: additive, dense, pseudorandom
aka: energy increment, structured plus pseudorandom plus small decomposition, regularity-type decompositions, Szemerédi-type theorems, primes
- What: decompose into structured + pseudorandom + small parts; each iteration raises a bounded energy.
- Fits when: regularity-type decompositions in any setting.
- Lean: —
- Example: Tao's unified account of Szemerédi-type theorems and the primes ([arXiv:math/0512114](https://arxiv.org/abs/math/0512114), [arXiv:0707.4269](https://arxiv.org/abs/0707.4269)).
- See also: T352, T412, T320

### T414 Gowers uniformity norms and inverse theorems
`prove` `bound` · stage: argue · signals: additive, dense, pseudorandom
aka: U^k norms, higher-order Fourier analysis, inverse theorem, nilsequences, Green–Tao–Ziegler, quantitative Szemerédi theorem, long progressions
- What: count k-term patterns via U^{k-1} norms; a large norm means correlation with a nilsequence.
- Fits when: longer progressions or complexity-≥2 linear patterns.
- Lean: —
- Example: Gowers' quantitative Szemerédi theorem; the Green–Tao–Ziegler inverse theorem ([Wikipedia: Gowers norm](https://en.wikipedia.org/wiki/Gowers_norm), [arXiv:1009.3998](https://arxiv.org/abs/1009.3998)).
- See also: T412, T415, T824

### T415 Transference
`prove` · stage: reformulate · signals: additive, integers, sparse, pseudorandom
aka: dense model theorem, embed the sparse set in a dense pseudorandom one, pseudorandom majorant, relative Szemerédi theorem, Green–Tao theorem, Reingold–Trevisan–Tulsiani–Vadhan
- What: a dense subset of a pseudorandom set behaves like a dense subset of everything.
- Fits when: sparse sets (primes) that sit inside a pseudorandom majorant; a dense-case theorem exists.
- Lean: —
- Example: Green–Tao: the primes contain arbitrarily long progressions ([arXiv:math/0404188](https://arxiv.org/abs/math/0404188), [Wikipedia: Green–Tao theorem](https://en.wikipedia.org/wiki/Green%E2%80%93Tao_theorem)); the dense model theorem of Reingold–Trevisan–Tulsiani–Vadhan ([ECCC TR08-045](https://eccc.weizmann.ac.il/report/2008/045/)).
- See also: T414, T357, T507

### T416 Plünnecke–Ruzsa sumset calculus
`bound` · stage: argue · signals: additive, inequality
aka: Plünnecke–Ruzsa inequality, Ruzsa triangle inequality, Ruzsa covering lemma, small doubling, iterated sumsets, Petridis' proof
- What: small doubling controls all iterated sumsets; Ruzsa's triangle inequality and covering lemma move between sets.
- Fits when: any problem with |A + A| ≤ K|A|.
- Lean: Mathlib: `Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul`, `Finset.ruzsa_triangle_inequality_div_div_div` (`Combinatorics/Additive/PluenneckeRuzsa.lean`), `Finset.ruzsa_covering_mul` (`RuzsaCovering.lean`).
- Example: Petridis' short proof of the Plünnecke–Ruzsa inequalities ([arXiv:1101.3507](https://arxiv.org/abs/1101.3507), [Wikipedia: Plünnecke–Ruzsa inequality](https://en.wikipedia.org/wiki/Plünnecke–Ruzsa_inequality)).
- See also: T417, T421, T622

### T417 Freiman structure theorems
`prove` · stage: argue · signals: additive, classification
aka: Freiman's theorem, Freiman homomorphisms, Ruzsa modelling, generalized arithmetic progressions, inverse sumset problems
- What: sets of small doubling sit efficiently in generalized progressions; Freiman homomorphisms move them into small groups.
- Fits when: inverse sumset problems.
- Lean: Mathlib defines Freiman homomorphisms (`IsAddFreimanHom`, `Combinatorics/Additive/FreimanHom.lean`).
- Example: Freiman's theorem and Ruzsa's proof via modelling plus Bogolyubov ([Wikipedia: Freiman's theorem](https://en.wikipedia.org/wiki/Freiman's_theorem)).
- See also: T416, T418, T425

### T418 Bogolyubov–Ruzsa lemma with Bohr sets
`prove` `bound` · stage: argue · signals: additive, finite-field
aka: Bogolyubov's lemma, Bohr sets, coset progressions, 2A − 2A, quasi-polynomial Bogolyubov–Ruzsa
- What: 2A - 2A contains a large structured set (Bohr set or coset progression).
- Fits when: finding structure from small doubling with good bounds.
- Lean: —
- Example: Sanders' quasi-polynomial Bogolyubov–Ruzsa lemma ([arXiv:1011.0107](https://arxiv.org/abs/1011.0107)).
- See also: T417, T419

### T419 Almost periodicity of convolutions
`bound` · stage: argue · signals: additive, random
aka: Croot–Sisask lemma, random sampling, translates, Sanders' Roth bound, probabilistic proof of Roth's theorem, nonabelian settings
- What: random sampling shows convolutions are nearly invariant under many translates, without Fourier analysis.
- Fits when: nonabelian settings or when Fourier bounds lose too much.
- Lean: —
- Example: Sanders' Roth bound N/(log N)^{3/4-o(1)}; probabilistic proof of Roth's theorem ([arXiv:1003.2978](https://arxiv.org/abs/1003.2978), [arXiv:1007.5444](https://arxiv.org/abs/1007.5444)).
- See also: T418, T420

### T420 Sifting and spectral positivity
`bound` · stage: argue · signals: additive, dense
aka: Kelley–Meka method, sifting, spectral positivity, density increment with spectral positivity, quasi-polynomial Roth bound, Bloom–Sisask, log barrier for Roth
- What: find a large subset where the set's convolution has positive, structured behaviour, then density-increment with quasi-polynomial loss.
- Fits when: 3-AP-type problems needing near-Behrend bounds.
- Lean: —
- Example: 3-AP-free sets have density at most exp(-c(log N)^β) ([arXiv:2302.05537](https://arxiv.org/abs/2302.05537)); previously Bloom–Sisask broke the log barrier ([arXiv:2007.03528](https://arxiv.org/abs/2007.03528)).
- See also: T412, T424, T309

### T421 Entropic sumset theory
`prove` `bound` · stage: argue · signals: additive, finite-field, random
aka: entropic Ruzsa distance, entropy sumset inequalities, polynomial Freiman–Ruzsa conjecture, Marton's conjecture, PFR
- What: replace sets by random variables and cardinality by entropy; entropic Ruzsa distance has clean calculus.
- Fits when: inverse theorems where combinatorial losses compound.
- Lean: the PFR theorem is formalized in Lean 4 ([PFR project](https://teorth.github.io/pfr/)), outside Mathlib.
- Example: Gowers–Green–Manners–Tao proof of Marton's (polynomial Freiman–Ruzsa) conjecture ([arXiv:2311.05762](https://arxiv.org/abs/2311.05762)).
- See also: T364, T416, T417

### T422 Sum-product via incidence geometry
`bound` · stage: reformulate · signals: additive, geometry
aka: Erdős–Szemerédi sum-product conjecture, Elekes' bound, Szemerédi–Trotter theorem, multiplicative energy, Solymosi
- What: encode a + b and a·b relations as point-line incidences and apply Szemerédi–Trotter.
- Fits when: mixed additive/multiplicative structure.
- Lean: —
- Example: Elekes' bound; Solymosi's max(|A+A|,|AA|) ≥ |A|^{4/3-ε} via multiplicative energy ([Wikipedia: Erdős–Szemerédi theorem](https://en.wikipedia.org/wiki/Erdős–Szemerédi_theorem), [arXiv:0806.1040](https://arxiv.org/abs/0806.1040)).
- See also: T738, T739, T396

### T423 Transformations of sumsets
`prove` `bound` · stage: argue · signals: additive, group, inequality
aka: Dyson e-transform, Kneser's theorem, stabilizers, Cauchy–Davenport theorem, sumset lower bounds in abelian groups
- What: transform a pair (A, B) to one with smaller sumset and induct; stabilizers explain the extremal cases.
- Fits when: exact lower bounds for |A + B| in abelian groups.
- Lean: Mathlib: the Dyson e-transform `mulDysonETransform` and its additive version (`Combinatorics/Additive/ETransform.lean`), `ZMod.cauchy_davenport` (`CauchyDavenport.lean`).
- Example: Kneser's theorem with its stabilizer term; Dyson's transform for Cauchy–Davenport in general groups ([Wikipedia: Kneser's theorem](https://en.wikipedia.org/wiki/Kneser's_theorem_%28combinatorics%29), [Wikipedia: Cauchy–Davenport theorem](https://en.wikipedia.org/wiki/Cauchy–Davenport_theorem)).
- See also: T391, T416

### T424 Behrend-type constructions
`find` `bound` · stage: construct · signals: additive, geometry, construction
aka: Behrend's construction, Salem–Spencer sets, 3-AP-free sets, points on a sphere, strictly convex surfaces, Roth number lower bounds
- What: map integers to points on a high-dimensional sphere so progressions become collinear triples on a strictly convex surface.
- Fits when: lower bounds for pattern-free sets.
- Lean: Mathlib: `Behrend.roth_lower_bound` (`Combinatorics/Additive/AP/Three/Behrend.lean`).
- Example: Behrend's 3-AP-free set of size N exp(-c√log N) ([Wikipedia: Salem–Spencer set](https://en.wikipedia.org/wiki/Salem–Spencer_set)).
- See also: T311, T412, T420

### T425 Growth in groups and approximate groups
`prove` `bound` · stage: argue · signals: group, additive, classification
aka: approximate groups, small tripling, Helfgott's growth theorem, SL_2(F_p), Breuillard–Green–Tao, Cayley graph diameter, expansion, nonabelian Freiman problems
- What: small tripling forces structure (subgroups, nilpotent progressions); otherwise sets grow fast.
- Fits when: diameter and expansion of Cayley graphs, nonabelian Freiman problems.
- Lean: Mathlib defines approximate subgroups (`IsApproximateSubgroup`, `Combinatorics/Additive/ApproximateSubgroup.lean`).
- Example: Helfgott's growth in SL_2(F_p); Breuillard–Green–Tao structure of approximate groups ([arXiv:math/0509024](https://arxiv.org/abs/math/0509024), [arXiv:1110.5008](https://arxiv.org/abs/1110.5008)).
- See also: T407, T417, T579

### T426 Additive combinatorics inside arithmetic geometry
`prove` · stage: argue · signals: arithmetic-geometry, additive, logic
aka: Selmer ranks in families, 2-descent statistics, rank growth across twists, Hilbert's tenth problem over rings, Koymans–Pagano
- What: control Selmer ranks in families by bilinear/additive-combinatorial estimates.
- Fits when: statistics of 2-descent or rank growth across twists.
- Lean: —
- Example: Koymans–Pagano: Hilbert's tenth problem is undecidable over every infinite finitely generated ring ([arXiv:2412.01768](https://arxiv.org/abs/2412.01768)).
- See also: T515, T771
