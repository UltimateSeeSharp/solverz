# Finite reduction, then a certificate
A theoretical reduction to finitely many cases, then exhaustive search or SAT, then a formal or checkable certificate (S19–S25). Referees of a huge computation may stay only "99% certain" until a formal check (S20).
Stuck on a statement over infinitely many cases: push the analysis until the finite range fits the machine (S25), and make the check one that others can rerun.

### S19 Four colour theorem
Stuck: 1852–1976 · `prove` · used: T464, T334, T120
- Unlock: Kempe's 1879 proof was flawed; Heesch's discharging and reducibility made a finite unavoidable set; Appel–Haken checked it by computer; later 633 configurations; Coq in 2005.
- From: computing.
- Source: [Wikipedia: Four color theorem](https://en.wikipedia.org/wiki/Four_color_theorem)

### S20 Kepler conjecture
Stuck: 1611–1998 (formal 2014) · `prove` · used: T324, T35, T1346
- Unlock: Fejes Tóth's 1953 reduction to finitely many configurations; Hales–Ferguson checked over 5,000 with about 100,000 linear programs; referees were only "99% certain", so Flyspeck formalised it in HOL Light and Isabelle.
- From: optimisation and computing, then formal proof.
- Source: [Wikipedia: Kepler conjecture](https://en.wikipedia.org/wiki/Kepler_conjecture)

### S21 Boolean Pythagorean triples
Stuck: 1980s–2016 · `compute` · used: T3, T4
- Unlock: 7825 is the threshold; symmetry and reasoning cut 10²³⁵⁵ colourings to about a trillion SAT cases; cube-and-conquer, 4 CPU-years, a 200 TB proof. Schur number five followed (2 PB).
- From: SAT solving, by computer scientists.
- Source: [Wikipedia: Boolean Pythagorean triples problem](https://en.wikipedia.org/wiki/Boolean_Pythagorean_triples_problem), [Wikipedia: Schur number](https://en.wikipedia.org/wiki/Schur_number)

### S22 Keller's conjecture
Stuck: 1930–2020 · `compute` · used: T1001, T119, T6
- Unlock: Corrádi–Szabó turned it into cliques in Keller graphs; counterexamples in dimension 10 (1992) and 8 (2002) showed it false there (S4); dimension 7 was proved true by SAT in 2020.
- From: a graph reduction, then SAT.
- Source: [Wikipedia: Keller's conjecture](https://en.wikipedia.org/wiki/Keller%27s_conjecture)

### S23 Busy Beaver BB(5)
Stuck: 1962–2024 (champion machine 1989) · `compute` · used: T37, T120, T1355
- Unlock: classify all 5-state machines with deciders, every one checked in Coq/Rocq, using `native_compute`.
- From: an online collaborative group of amateurs (bbchallenge).
- Source: [Wikipedia: Busy beaver](https://en.wikipedia.org/wiki/Busy_beaver), [arXiv:2509.12337](https://arxiv.org/abs/2509.12337)

### S24 Rupert property for convex polyhedra
Stuck: 2017–2025 (question since Prince Rupert's cube) · `find` · used: T1306, T324, T1370
- Unlock: a 90-vertex point-symmetric "Noperthedron" lacks the property, so the conjecture was false (S4); symmetry cuts the 5-parameter space, which splits into ~18 million regions, each excluded by a global or local theorem with rational arithmetic.
- From: computer-assisted case analysis.
- Source: [arXiv:2508.18475](https://arxiv.org/html/2508.18475)

### S25 Ternary Goldbach
Stuck: 1742–2013 · `prove` · used: T481, T324
- Unlock: Helfgott pushed explicit circle-method bounds down until they met a computer verification (with Platt).
- From: analytic number theory plus computation.
- Source: [arXiv:1312.7748](https://arxiv.org/abs/1312.7748)
