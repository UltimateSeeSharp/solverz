# Certificate design for Lean's kernel
Turning an untrusted computation into something Lean's kernel checks cheaply: what to ship, how to pack it, how to split and shrink it.

### T118 Witness certificates
`find` · stage: certify · signals: construction
aka: explicit witness, counterexample, find-problem certificate, sums of three cubes, Euler quartic counterexamples, Ramsey colourings, matrix multiplication schemes
- What: ship the object; Lean checks the property.
- Fits when: find problems and counterexamples.
- Lean: `norm_num`, `decide +kernel`, `ring`.
- Example: sums of three cubes ([Booker](https://arxiv.org/abs/1903.04284)), Euler quartic counterexamples, Ramsey colourings and flip-graph matrix schemes ([Kauers–Moosbauer](https://arxiv.org/abs/2212.01175)).
- See also: T40, T121, T124

### T119 Prove the reduction, not the search
`prove` `compute` · stage: certify · signals: local-constraints, impossibility
aka: verified encodings, Trestle, VEncCNF, encoding correctness, reduction to a finite problem, empty hexagon h(6)=30, Keller's conjecture, R(4,5) in HOL4, precedents of verified computation
- What: formalize the map from the statement to a finite problem and its encoding, and prove it correct in Lean; only the certificate check then remains, and most of the human-level reasoning goes here.
- Fits when: every computational proof, and whenever a SAT result must count.
- Lean: formalize statement → finite problem → encoding; Trestle's `VEncCNF` ties encodings to a propositional model (pins Lean v4.21.0, needs a port); the solver stays untrusted.
- Example: the empty hexagon number h(6)=30 (17,300 CPU-hours) with a Lean-verified encoding; its SAT proofs went through cake_lpr, and UNSAT is asserted as an axiom in Lean ([Heule–Scheucher](https://arxiv.org/abs/2403.00737); [Lean verification](https://arxiv.org/abs/2403.17370)); Keller's conjecture end to end in Lean 4 for all dimensions, with certificates checked by cake_lpr and Trestle's LSR checker ([ITP 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.26); [Trestle](https://github.com/FormalSAT/trestle)); neither is kernel-only by this repo's rules.
- See also: T5, T10, T120, T122

### T120 Verified checker run in the kernel
`prove` `compute` · stage: certify
aka: proof by reflection, certifying algorithms, untrusted oracle plus verified checker, decide +kernel, four colour theorem, Flyspeck, BB(5), Keller n = 8
- What: write the checker in Lean, prove it sound, and reduce it in the kernel on small data.
- Fits when: case analyses with uniform structure.
- Lean: `decide +kernel` on a structurally recursive (or fuelled) checker with a `decidable_of_iff` instance; well-founded recursion may fail or be slow (on a `Nat` measure it often works, e.g. core `Nat.powMod`: test it); `Eq.rec` left by `rw`/`simp` can get stuck.
- Example: the four colour theorem, fully checked in Coq by reflection ([Gonthier](https://www.cl.cam.ac.uk/~lp15/Pages/4colproof.pdf)); lrat-catcher `+kernel` runs Lean core's verified LRAT checker in the kernel ([lrat-catcher](https://github.com/leansolving/lrat-catcher)); the Keller n = 8 counterexample check in Lean 4 ([ITP 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.26)); other precedents: Flyspeck in HOL Light/Isabelle ([Flyspeck](https://arxiv.org/abs/1501.02155)), R(4,5) in HOL4 ([Gauthier–Brown](https://arxiv.org/abs/2404.01761)), BB(5) in Coq with `native_compute`, which would not count here ([bbchallenge](https://arxiv.org/abs/2509.12337)); `decide +kernel` semantics ([Init/Tactics.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Tactics.lean)).
- See also: T5, T119, T121, T122, T127

### T121 Kernel-friendly data layout
`prove` `find` `compute` · stage: certify · signals: set-family, graph, colouring
aka: bitsets, bitmasks, packed arrays, GMP fast path, Nat literals, kernel reduction, decide performance, adjacency bitmasks, packed sieves
- What: pack sets, graphs and colourings into `Nat` bitmasks and compute with `land`/`lor`/`xor`/shifts/`mod`; avoid `List`/`Finset` enumeration over big ranges, well-founded recursion and `Eq.rec`-laden instances.
- Fits when: every `decide`-style check.
- Lean: the kernel evaluates `Nat` `succ add sub mul div mod gcd beq ble land lor xor shiftLeft shiftRight pow` on literals with GMP; results capped at 128 MB (`LEAN_NAT_MAX_SIZE`, configurable); `pow`/`shiftLeft` need an exponent below 2^32; every other function unfolds by its definition.
- Example: the GMP fast path in the kernel source ([type_checker.cpp](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)); the reference manual lists fewer accelerated functions, and the kernel source is the authority ([Natural Numbers](https://lean-lang.org/doc/reference/4.35.0/Basic-Types/Natural-Numbers/)).
- See also: T120, T122

### T122 Split into many theorems
`prove` `compute` · stage: certify
aka: parallel checking, chunked certificates, one module per cube, covering lemma, independently checkable pieces, checking cheaper than searching
- What: split a certificate into many small theorems, each checked on its own, plus one lemma that the pieces cover everything; checking must be far cheaper than searching.
- Fits when: any certificate above about a minute of kernel time.
- Lean: one theorem per cube, orbit or case, in separate modules, plus one covering lemma; `lake build` checks independent modules in parallel.
- Example: lrat-catcher puts one module per cube "so the per-cube refutations build concurrently under `lake`" ([lrat-catcher](https://github.com/leansolving/lrat-catcher)); ETP's millions of small facts ([ETP](https://arxiv.org/abs/2512.07087)).
- See also: T3, T18, T38, T120

### T123 Shrink witnesses and certificates
`find` `prove` · stage: certify · signals: graph, colouring, construction
aka: proof minimization, UNSAT cores, witness shrinking, delta debugging, trimming, drat-trim cores, viprttn, certificate compression, unit-distance graphs, chromatic number of the plane, Hadwiger–Nelson problem
- What: deletes parts of an object while keeping its property (UNSAT cores), and trims proofs and certificates to the steps the conclusion needs.
- Fits when: a small object is the goal or the certificate; SAT, MIP and game proofs before they go to Lean.
- Lean: kernel time scales with certificate size; unit distances by exact algebra (`ring`/`norm_num`), non-colourability by a small LRAT (T5).
- Example: 5-chromatic unit-distance graphs cut from de Grey's 1,581 vertices to 553, validated in about a second ([Heule](https://arxiv.org/abs/1805.12181)), later to 509 by Parts's graph minimization ([arXiv:2010.12665](https://arxiv.org/abs/2010.12665)); drat-trim cores ([drat-trim](https://github.com/marijnheule/drat-trim)); VIPR's `viprttn` ([scipopt/vipr](https://github.com/scipopt/vipr)); the checkers proof's stored 10⁷ positions (T117).
- See also: T4, T49, T117, T118

### T124 Exact rational rounding
`bound` `prove` · stage: certify · signals: inequality, matrix, numeric-only
aka: rounding pipeline, float to rational, Peyrl–Parrilo rounding, rational SOS, exact Gram matrix, rational witnesses, explicit constants, π bounds, sqrtTwoAddSeries
- What: float solver → rational rounding (for SOS, project the numerical Gram matrix to an exact rational one) → exact re-check outside Lean → Lean checks a short chain of rational facts.
- Fits when: LP, SDP, SOS and interval output must become a proof; explicit constants inside proofs.
- Lean: rational witnesses checked by `norm_num`, `linarith` or `ring`; it fails fast if the rounding is wrong, so tune it in scratch first.
- Example: Peyrl–Parrilo give the rounding tolerance that guarantees an exact SOS ([TCS 2008](https://portal.mardi4nfdi.de/wiki/Publication:2378506)); Mathlib bounds π to 20 decimals via `sqrtTwoAddSeries`, using witnesses generated in Mathematica ([Pi bounds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Pi/Bounds.html)).
- See also: T48, T52, T54, T99

### T125 Short proofs of long computations
`compute` `prove` · stage: certify · signals: integers
aka: proofs of exponentiation, Pietrzak proofs, verifiable delay, Gerbicz error check, PRP proofs, GIMPS, Mersenne primes, delegated computation
- What: a proof of exponentiation or a delegated computation that the verifier checks in a fraction of the time.
- Fits when: huge deterministic exponentiations, where rerunning is the cost; designing checkable certificates.
- Lean: none directly at this scale; verifying with the certificate's help is the idea that carries over.
- Example: the Mersenne prime M136279841, found by Durant on cloud GPUs in 2024 ([GIMPS](https://www.mersenne.org/primes/?press=M136279841)); a PRP proof checks in about 1/100 of the original time ([GIMPS overview](https://en.wikipedia.org/wiki/Great_Internet_Mersenne_Prime_Search)).
- See also: T43, T126

### T126 Randomized checks as filters
`prove` `find` · stage: certify · signals: polynomial, matrix
aka: Schwartz–Zippel, Freivalds, polynomial identity testing, probabilistic checks, probable-prime tests, screening candidates
- What: Schwartz–Zippel or Freivalds checks screen candidates fast; a failed check is a definite disproof (the failing point is a checkable witness), a passed check proves nothing.
- Fits when: pruning before an exact check.
- Lean: a pass never counts; a failing point can serve as an exact witness of non-identity.
- Example: GIMPS probable-prime hits count only after Lucas–Lehmer confirmation ([GIMPS](https://www.mersenne.org/primes/?press=M136279841)).
- See also: T118, T125
