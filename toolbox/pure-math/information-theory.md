# Information theory
Divergence inequalities, information lower bounds, entropy-region inequalities, entropy power and large deviations of empirical measures; entropy counting itself is in extremal combinatorics.

### T795 Information inequalities (Pinsker, KL divergence)
`bound` `prove` · stage: argue · signals: random, inequality
aka: Pinsker's inequality, Kullback–Leibler divergence, relative entropy, total variation distance, structured versus uniform distributions
- What: relates distances between distributions to entropy and divergence.
- Fits when: comparing a structured distribution with a uniform one.
- Lean: Mathlib: `InformationTheory.klDiv` and its data-processing inequality `InformationTheory.klDiv_map_le`; Pinsker is not there (grep).
- Example: Pinsker's inequality ([Wikipedia: Pinsker's inequality](https://en.wikipedia.org/wiki/Pinsker's_inequality)).
- See also: T364, T796, T799

### T796 Fano's inequality and data processing
`bound` · stage: argue · signals: random, inequality, impossibility, resource-bound
aka: Fano's inequality, data processing inequality, minimax lower bounds, query lower bounds, sample complexity, communication lower bounds, distinguishable hypotheses
- What: an estimator with small error must carry information, and processing cannot add information; together they turn "too little information" into lower bounds.
- Fits when: lower bounds on queries, samples, communication or the number of distinguishable hypotheses.
- Lean: Mathlib has the data-processing inequality for KL divergence (`InformationTheory.klDiv_map_le`); Fano is not there (grep).
- Example: lower bounds on decoder error and on minimax risk in density estimation ([Wikipedia: Fano's inequality](https://en.wikipedia.org/wiki/Fano%27s_inequality), [Wikipedia: Data processing inequality](https://en.wikipedia.org/wiki/Data_processing_inequality)).
- See also: T795, T768

### T797 Entropic vectors and non-Shannon inequalities
`bound` `prove` · stage: argue · signals: random, inequality, set-family
aka: entropy region, polymatroids, Shannon-type inequalities, Zhang–Yeung inequality, Dougherty–Freiling–Zeger, secret sharing, network coding, Han's inequality
- What: the entropy region of n variables obeys the Shannon inequalities and, from n = 4 on, further non-Shannon ones; a Shannon-type inequality is a nonnegative combination of basic ones.
- Fits when: Shearer- or Han-type arguments almost close; secret-sharing, network-coding or polymatroid bounds.
- Lean: a Shannon-type inequality comes with an LP certificate (nonnegative multipliers of basic inequalities), checked by `linarith` or exact arithmetic (T48).
- Example: Zhang–Yeung's first non-Shannon inequality; Dougherty–Freiling–Zeger list more in four variables ([Wikipedia: Entropic vector](https://en.wikipedia.org/wiki/Entropic_vector), [arXiv:1104.3602](https://arxiv.org/abs/1104.3602)).
- See also: T364, T48, T128

### T798 Entropy power inequality
`bound` `prove` · stage: argue · signals: random, analytic, inequality, additive
aka: EPI, Shannon–Stam inequality, entropy power, Brunn–Minkowski analogue, Costa–Cover, CLT monotonicity, sums of independent vectors
- What: the entropy power of a sum of independent vectors is at least the sum of their entropy powers, an information-theoretic twin of Brunn–Minkowski.
- Fits when: continuous additive problems, sums of independent variables, CLT-type monotonicity.
- Lean: —
- Example: Shannon's inequality with Stam's equality case; its analogy with Brunn–Minkowski (Costa–Cover) ([Wikipedia: Entropy power inequality](https://en.wikipedia.org/wiki/Entropy_power_inequality)).
- See also: T611, T421

### T799 Sanov's theorem
`bound` `compute` · stage: argue · signals: random, asymptotic, sequence
aka: large deviations of empirical measures, method of types, KL rate function, sequences with prescribed statistics, exponential-precision counting
- What: the probability that a sample's empirical distribution lies in a set decays at the rate of the smallest KL divergence to that set.
- Fits when: exponential-precision counts of sequences with prescribed statistics.
- Lean: —
- Example: the rate function for empirical measures ([Wikipedia: Sanov's theorem](https://en.wikipedia.org/wiki/Sanov%27s_theorem)).
- See also: T777, T795
