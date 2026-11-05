# Machine learning for conjectures
Trained models and fitted formulas that point to patterns; the theorem is then proved conventionally.

### T86 Supervised learning plus attribution
`prove` · stage: explore · signals: topology, group
aka: saliency, feature attribution, AI-guided intuition, knot invariants, knot signature, hyperbolic invariants, natural slope, Kazhdan–Lusztig hypercube conjecture
- What: trains a model to predict Y from X; saliency shows which features matter, and the mathematician conjectures from them.
- Fits when: rich computable invariants with a suspected link.
- Lean: the theorem is proved conventionally; ML only points the way.
- Example: knot signature from hyperbolic invariants (78% accuracy against a 25% baseline) led to the "natural slope" theorem, plus a Kazhdan–Lusztig hypercube conjecture ([Davies et al.](https://pmc.ncbi.nlm.nih.gov/articles/PMC8636249/)).
- See also: T80, T89

### T87 Data exploration of arithmetic databases
`prove` · stage: explore · signals: arithmetic-geometry
aka: murmurations, elliptic curves, Frobenius traces, averages over families, rank, arithmetic statistics, LMFDB data
- What: averages over large families reveal structure.
- Fits when: number-theoretic statistics.
- Lean: conjecture source only.
- Example: the rank-dependent oscillating Frobenius-trace averages called "murmurations" ([He–Lee–Oliver–Pozdnyakov](https://arxiv.org/abs/2204.10140)).
- See also: T81, T86

### T88 Symbolic regression
`compute` · stage: explore · signals: analytic, identity
aka: AI Feynman, PySR, formula discovery, closed-form fitting, symmetry and separability
- What: searches for formulas that fit data, using symmetry and separability.
- Fits when: guessing closed forms of computed functions.
- Lean: the formula is a conjecture; prove it.
- Example: AI Feynman recovered all 100 Feynman-lecture equations, and lifted a harder set from 15% to 90% ([Udrescu–Tegmark](https://arxiv.org/abs/1905.11481); [PySR](https://arxiv.org/abs/2305.01582)).
- See also: T62, T93

### T89 Mechanistic interpretability as discovery
`prove` · stage: explore · signals: integers, group
aka: reverse-engineering neural networks, modular addition, discrete Fourier transform, rotation about a circle, GCD learning, divisor products
- What: reverse-engineers the algorithm a trained net uses.
- Fits when: a net solves a task better than known heuristics.
- Lean: the extracted algorithm is proved correct conventionally.
- Example: modular addition is learned as discrete Fourier rotation ([Nanda et al.](https://arxiv.org/abs/2301.05217)); GCD is learned as a list of divisor products ([Charton](https://arxiv.org/abs/2308.15594)).
- See also: T86
