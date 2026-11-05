# An imported tool
A technique native to another field meets a problem whose specialists had never used it (S26–S43). Outsiders win by carrying a tool, not domain knowledge; Marcus "couldn't have told you what the problem was" in the field's language ([Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/)). They enter through a reformulation in neutral language (vectors, graphs, SAT, entropy) that insiders wrote first.
Stuck within one field's methods: restate the problem in a neutral, checkable language, scan other fields' tools against it, and read the insiders' reductions first.

### S26 Poincaré conjecture
Stuck: 1904–2003 · `prove` · used: T686
- Unlock: Hamilton's Ricci flow (1982) stalled on singularities; Perelman added a monotone entropy-like quantity, classified the singularities, did surgery and showed finite extinction.
- From: the heat equation and statistical mechanics (his quantity is "an entropy for a certain canonical ensemble").
- Source: [Wikipedia: Poincaré conjecture](https://en.wikipedia.org/wiki/Poincar%C3%A9_conjecture), [arXiv:math/0211159](https://arxiv.org/abs/math/0211159)

### S27 3-term progressions (Kelley–Meka)
Stuck: 1953–2023 (log barrier fell only in 2020) · `bound` · used: T420, T309
- Unlock: a density increment driven by "sifting" (repeated shift-and-intersect), developed first over finite fields; the bound is nearly Behrend-shaped.
- From: complexity-theory tools, by two computer scientists, one a grad student.
- Source: [Quanta](https://www.quantamagazine.org/surprise-computer-science-proof-stuns-mathematicians-20230321/), [arXiv:2302.05537](https://arxiv.org/abs/2302.05537)

### S28 Off-diagonal Ramsey R(4, t)
Stuck: long-standing exponent 5/2, to 2023 · `bound` · used: T388
- Unlock: a pseudorandom graph from Hermitian unitals in finite geometry, plus random choices, gives Ω(t³/log⁴ t).
- From: finite geometry.
- Source: [arXiv:2306.04007](https://arxiv.org/abs/2306.04007)

### S29 Green–Tao theorem
Stuck: about 1770–2004 · `prove` · used: T415, T507
- Unlock: a relative Szemerédi theorem (transference) for sets dense inside a pseudorandom set, plus a pseudorandom set containing the primes built from GPY ideas.
- From: Szemerédi's theorem combined with sieve theory.
- Source: [Wikipedia: Green–Tao theorem](https://en.wikipedia.org/wiki/Green%E2%80%93Tao_theorem)

### S30 Kadison–Singer problem
Stuck: 1959–2013 · `prove` · used: T403, T304, T783, T1374
- Unlock: Weaver's finite discrepancy reformulation; interlacing families of real-rooted mixed characteristic polynomials, after five years of work; the same method gave bipartite Ramanujan graphs. Most expected "no"; the doubted claim was true.
- From: graph sparsification and electrical networks; Kalai spotted the link. Three computer scientists used "tools none of us had ever heard of".
- Source: [Quanta](https://www.quantamagazine.org/computer-scientists-solve-kadison-singer-problem-20151124/), [Wikipedia: Kadison–Singer problem](https://en.wikipedia.org/wiki/Kadison%E2%80%93Singer_problem), [arXiv:1408.4421](https://arxiv.org/abs/1408.4421)

### S31 Erdős discrepancy problem
Stuck: about 1932–2015 · `prove` · used: T495, T494, T1355, T1374
- Unlock: Polymath5 reduced it to (stochastic) completely multiplicative functions; a blog comment suggested Matomäki–Radziwiłł; Tao proved a log-averaged Elliott conjecture with an entropy decrement argument. SAT had settled only C = 2 (1160 terms).
- From: information theory (entropy) plus open collaboration.
- Source: [Quanta](https://www.quantamagazine.org/a-magical-answer-to-an-80-year-old-puzzle-20151001/), [arXiv:1509.05363](https://arxiv.org/abs/1509.05363), [Wikipedia: Erdős discrepancy problem](https://en.wikipedia.org/wiki/Erd%C5%91s_discrepancy_problem)

### S32 Weil conjectures, Riemann hypothesis part
Stuck: 1949–1974 · `prove` · used: T310, T1340, T622, T1342
- Unlock: Weil's topological analogy demanded a cohomology for varieties over finite fields; Grothendieck built étale cohomology; Deligne bypassed the standard conjectures with Lefschetz pencils and Rankin's 1939 tensor-power trick from modular forms.
- From: topology, by analogy.
- Source: [Wikipedia: Weil conjectures](https://en.wikipedia.org/wiki/Weil_conjectures)

### S33 PRIMES is in P
Stuck: to 2002 · `prove` · used: T1066
- Unlock: test the polynomial identity (X + a)ⁿ ≡ Xⁿ + a modulo (Xʳ − 1, n); earlier fast tests needed randomness or an unproven GRH.
- From: computer scientists at IIT Kanpur; Kayal and Saxena were students.
- Source: [Wikipedia: AKS primality test](https://en.wikipedia.org/wiki/AKS_primality_test), [Wikipedia: Neeraj Kayal](https://en.wikipedia.org/wiki/Neeraj_Kayal)

### S34 Sphere packing in dimensions 8 and 24
Stuck: to 2016 · `bound` · used: T562, T50, T1373, T1312
- Unlock: the Cohn–Elkies linear-programming bound needed a "magic" function vanishing with its Fourier transform on lattice shells; Viazovska built it as a Laplace transform of modular forms.
- From: modular forms meeting an optimisation dual.
- Source: [Wikipedia: Sphere packing](https://en.wikipedia.org/wiki/Sphere_packing), [arXiv:1603.04246](https://arxiv.org/abs/1603.04246)

### S35 Robbins conjecture
Stuck: 1933–1996 · `prove` · used: T17
- Unlock: the automated prover EQP found the proof in eight days, building on Winker's reductions.
- From: automated reasoning, by Argonne computer scientists.
- Source: [Wikipedia: Robbins algebra](https://en.wikipedia.org/wiki/Robbins_algebra)

### S36 Tait's conjectures
Stuck: 1890s–1987/1991 · `prove` · used: T837
- Unlock: the Jones polynomial settled the crossing-number conjecture for reduced alternating diagrams (Kauffman, Murasugi, Thistlethwaite); flyping fell in 1991.
- From: operator algebras: Jones found his polynomial in von Neumann algebras; Witten later read it from Chern–Simons theory.
- Source: [Wikipedia: Tait conjectures](https://en.wikipedia.org/wiki/Tait_conjectures), [Wikipedia: Jones polynomial](https://en.wikipedia.org/wiki/Jones_polynomial)

### S37 Continuum hypothesis
Stuck: 1900–1963 · `prove` · used: T762
- Unlock: forcing, a new way to build models of set theory, came when the problem was thought hopeless; it proved independence.
- From: an outsider: Cohen, a harmonic analyst (Zygmund student).
- Source: [Wikipedia: Forcing](https://en.wikipedia.org/wiki/Forcing_(mathematics)), [Wikipedia: Paul Cohen](https://en.wikipedia.org/wiki/Paul_Cohen)

### S38 Szemerédi's theorem
Stuck: 1936–1975 · `prove` · used: T480, T823, T414, T310
- Unlock: Roth (circle method, k = 3), Szemerédi (combinatorics), then more proofs: Furstenberg (ergodic theory), Gowers (Fourier analysis and Gowers norms, with bounds).
- From: each proof imported a different field; Tao calls them a Rosetta stone.
- Source: [Wikipedia: Szemerédi's theorem](https://en.wikipedia.org/wiki/Szemer%C3%A9di%27s_theorem)

### S39 Constructive Lovász local lemma
Stuck: 1975–2008 (Beck 1991 partial) · `find` · used: T381
- Unlock: resample a violated event; entropy compression shows the process must stop (Moser).
- From: information theory, via computer science.
- Source: [Wikipedia: Algorithmic Lovász local lemma](https://en.wikipedia.org/wiki/Algorithmic_Lov%C3%A1sz_local_lemma)

### S40 Duffin–Schaeffer conjecture
Stuck: 1941–2019 · `prove` · used: T502
- Unlock: Koukoulopoulos–Maynard controlled overlaps of approximation sets by encoding their GCD structure in graphs and iterating a compression argument.
- From: graph-theoretic structure inside metric number theory.
- Source: [Wikipedia: Duffin–Schaeffer theorem](https://en.wikipedia.org/wiki/Duffin%E2%80%93Schaeffer_theorem), [arXiv:1907.04593](https://arxiv.org/abs/1907.04593)

### S41 Connes' embedding conjecture
Stuck: decades, to 2020 · `prove` · used: T1051
- Unlock: MIP* = RE: quantum interactive proofs reduce the halting problem to nonlocal games, which refutes Tsirelson's problem and with it Connes; the conjecture was false (S4).
- From: quantum complexity theory, solving a problem of operator algebras.
- Source: [arXiv:2001.04383](https://arxiv.org/abs/2001.04383), [Wikipedia: Connes embedding problem](https://en.wikipedia.org/wiki/Connes_embedding_problem)

### S42 Polynomial Freiman–Ruzsa conjecture
Stuck: decades, to 2023 · `prove` · used: T421, T150
- Unlock: Gowers–Green–Manners–Tao used entropic Ruzsa distance; a public Lean blueprint project finished the formal proof by 5 December 2023, within a month of the preprint.
- From: entropy (information theory).
- Source: [arXiv:2311.05762](https://arxiv.org/abs/2311.05762), [Tao: PFR in Lean 4 with Blueprint](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/)

### S43 Alternating sign matrix conjecture
Stuck: 1983–1992 · `compute` · used: T802
- Unlock: Zeilberger's proof (1992), then Kuperberg's short proof (1995) via the six-vertex model and the Yang–Baxter equation.
- From: statistical mechanics, for the short proof.
- Source: [Wikipedia: Alternating sign matrix](https://en.wikipedia.org/wiki/Alternating_sign_matrix), [arXiv:math/9407211](https://arxiv.org/abs/math/9407211), [arXiv:math/9712207](https://arxiv.org/abs/math/9712207)
