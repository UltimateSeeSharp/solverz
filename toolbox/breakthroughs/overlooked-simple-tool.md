# An overlooked simple tool
After decades of heavy machinery the key was elementary: Cauchy interlacing, polynomial dimension counting, Shannon entropy (S44–S47), a 1976 special-function inequality (S59). Short "book" proofs often follow long stalls.
Stuck after heavy machinery failed: try an old, simple theorem from outside the field's fashion.

### S44 Cap set problem
Stuck: 1987–2016 · `bound` · used: T395, T309, T1375
- Unlock: Croot–Lev–Pach's polynomial method for Z₄ⁿ (2016), adapted by Ellenberg–Gijswijt to 2.756ⁿ; formalised in Lean in 2019. Lower bounds later moved by LLM-guided program search (T107).
- From: the polynomial method (linear-algebra dimension counting).
- Source: [Wikipedia: Cap set](https://en.wikipedia.org/wiki/Cap_set), [FunSearch](https://deepmind.google/discover/blog/funsearch-making-new-discoveries-in-mathematical-sciences-using-large-language-models/)

### S45 Sensitivity conjecture
Stuck: 1992–2019 · `prove` · used: T400, T1372, T304, T1027
- Unlock: Gotsman–Linial's reduction to induced subgraphs of the hypercube; Huang signed some entries of the adjacency matrix so that Cauchy interlacing gives degree ≥ √n. Two pages, after about seven years of returning to it.
- From: a 200-year-old linear-algebra theorem; a combinatorialist on a computer-science problem.
- Source: [Quanta](https://www.quantamagazine.org/mathematician-solves-computer-science-conjecture-in-two-pages-20190725/), [arXiv:1907.00847](https://arxiv.org/abs/1907.00847)

### S46 Kakeya: finite fields and R³
Stuck: 1999–2008 (finite fields); to 2025 (R³) · `bound` · used: T393, T305, T309, T640
- Unlock: a low-degree polynomial vanishing on a Kakeya set must be zero, so the set is large (Dvir, ~5 pages); Wang–Zahl later proved the 3D Euclidean conjecture via the sticky case.
- From: linear algebra over polynomials.
- Source: [Wikipedia: Kakeya set](https://en.wikipedia.org/wiki/Kakeya_set)

### S47 Union-closed sets conjecture
Stuck: 1979–2022 · `bound` · used: T364, T1376
- Unlock: if every element were rare, the union of two independent samples would carry more entropy than one, contradicting closure; this gave the constant 0.01, pushed to ~0.38 within days by others.
- From: information theory, by an outsider: Justin Gilmer, a Google ML researcher out of math for six years, working nights and weekends, back on the problem nine years after a failed year on it.
- Source: [Quanta](https://www.quantamagazine.org/long-out-of-math-an-ai-programmer-cracks-a-pure-math-problem-20230103/), [arXiv:2211.09055](https://arxiv.org/abs/2211.09055), [Wikipedia: Union-closed sets conjecture](https://en.wikipedia.org/wiki/Union-closed_sets_conjecture)
