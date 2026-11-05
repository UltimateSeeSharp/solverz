# Statistics of mathematical evidence
Judging computed evidence before it shapes a conjecture: small-case traps, null models, multiple testing, extrapolation, rare-event and exact sampling, plots, pre-registration.

### T1327 Strong law of small numbers
`prove` `find` · stage: explore
aka: small-n patterns, patterns that fail later, holds for all tested cases, Pólya conjecture, Haselgrove, Borwein integrals, sinc products
- What: small cases show patterns that later fail; agreement on small n is weak evidence.
- Fits when: a conjecture rests on small-n data or "holds for all tested cases"; push the data far past where the pattern "obviously" holds.
- Lean: — (a pass on small n proves nothing; a failure is a witness).
- Example: Pólya's conjecture fails first at n = 906,150,257 (Tanaka 1980), after Haselgrove disproved it in 1958; the Borwein integrals of products of sinc(x/(2k+1)) equal π/2 until the factor sinc(x/15) ([Wikipedia: Strong law of small numbers](https://en.wikipedia.org/wiki/Strong_law_of_small_numbers); [Wikipedia: Pólya conjecture](https://en.wikipedia.org/wiki/P%C3%B3lya_conjecture); [Wikipedia: Borwein integral](https://en.wikipedia.org/wiki/Borwein_integral)).
- See also: T136, T1324, T1370

### T1328 Null model and significance of a pattern
`prove` `compute` · stage: explore
aka: random model, Cramér-type heuristic, deviation from chance, significance, structure vs coincidence, Chebyshev's bias, prime races, logarithmic density
- What: compares an observed regularity with what the matching random model predicts, and measures the deviation, before calling it structure.
- Fits when: a striking pattern in primes, zeros or a database.
- Lean: —
- Example: Chebyshev's bias: primes ≡ 3 (mod 4) lead "more often than not"; the Knapowski–Turán claim that they lead on a set of density 1 is false, but that set has logarithmic density ≈ 0.9959, and even the bias is proved only under strong forms of the Riemann hypothesis ([Wikipedia: Chebyshev's bias](https://en.wikipedia.org/wiki/Chebyshev%27s_bias)).
- See also: T1302, T1329

### T1329 Multiple comparisons and held-out data
`compute` · stage: explore
aka: multiple testing, Bonferroni correction, false discovery rate, held-out data, data mining, mathematical coincidence, near-integers, e^{π√163}, Heegner numbers
- What: testing many candidate patterns on one data set guarantees false hits; correct for the number of tests (Bonferroni, false-discovery rate) and confirm on data that did not suggest the pattern.
- Fits when: mining OEIS, LMFDB, ML attributions or inverse-symbolic-calculator output.
- Lean: —
- Example: e^{π√163} is within about 10⁻¹² of an integer because 163 is a Heegner number, while a "mathematical coincidence" is by definition a near-equality "which has no apparent theoretical explanation" ([Wikipedia: Mathematical coincidence](https://en.wikipedia.org/wiki/Mathematical_coincidence); [Wikipedia: Multiple comparisons problem](https://en.wikipedia.org/wiki/Multiple_comparisons_problem)).
- See also: T77, T79, T86, T87

### T1330 Extrapolation of sequences
`bound` `compute` · stage: explore · signals: sequence, asymptotic
aka: Richardson extrapolation, ratio method, Padé approximants, DLog-Padé, series analysis, growth constant, critical exponent, Romberg integration
- What: fits the known asymptotic form to an exact initial segment to estimate the limit, growth constant or critical exponent, which then becomes the target to prove.
- Fits when: an enumeration gives 20–100 exact terms but no asymptotics; choosing what bound to aim for.
- Lean: — (an estimate; the bound is proved separately).
- Example: Romberg integration is Richardson extrapolation of the trapezoid rule; DLog-Padé approximants "extract critical points and exponents" from series ([Wikipedia: Richardson extrapolation](https://en.wikipedia.org/wiki/Richardson_extrapolation); [Wikipedia: Padé approximant](https://en.wikipedia.org/wiki/Pad%C3%A9_approximant)).
- See also: T62, T79

### T1331 Importance sampling for rare events
`find` `compute` · stage: explore · signals: random
aka: rare-event simulation, tilted distribution, likelihood ratio, reweighting, variance reduction, tiny probability gap, bunkbed conjecture
- What: samples from a tilted distribution that puts its mass on the rare region and reweights by the likelihood ratio, so tiny probabilities become measurable.
- Fits when: a counterexample would show only as a tiny probability gap, or a count is dominated by rare configurations.
- Lean: —
- Example: the standard variance-reduction method for rare-event simulation ([Wikipedia: Importance sampling](https://en.wikipedia.org/wiki/Importance_sampling)); the bunkbed counterexample's probability gap was far too small to sample ([Quanta](https://quantamagazine.org/maths-bunkbed-conjecture-has-been-debunked-20241101/)).
- See also: T1332, T1346

### T1332 Exact sampling by coupling from the past
`find` `compute` · stage: explore · signals: random
aka: CFTP, Propp–Wilson, perfect sampling, coalescence, coupled Markov chains, unbiased random instances, MCMC mixing, matchings, colourings, spin states
- What: runs coupled Markov chains from further and further back until all start states coalesce; the result is an exact draw from the stationary law, so statistics over random instances are unbiased.
- Fits when: testing a conjecture on uniformly random objects (matchings, colourings, spin states) when MCMC mixing is uncertain.
- Lean: —
- Example: Propp and Wilson's 1996 method gives "a perfect sample from the stationary distribution" ([Wikipedia: Coupling from the past](https://en.wikipedia.org/wiki/Coupling_from_the_past)).
- See also: T1331

### T1333 Plot it first
`find` `prove` `bound` `compute` · stage: explore
aka: visualization, plots, log-log plot, heat map of a table, Ulam spiral, prime spiral, Birch–Swinnerton-Dyer, EDSAC, look at the data
- What: draws the data (spirals, log-log plots, heat maps of tables) before fitting; the eye finds structure that summary statistics miss.
- Fits when: a large table of computed values exists and no hypothesis yet.
- Lean: —
- Example: Ulam's 1963 prime spiral shows dense diagonals that correspond to prime-rich quadratic polynomials ([Wikipedia: Ulam spiral](https://en.wikipedia.org/wiki/Ulam_spiral)); the Birch–Swinnerton-Dyer conjecture began from "somewhat tenuous trends in graphical plots" of EDSAC-2 point counts ([Wikipedia: Birch and Swinnerton-Dyer conjecture](https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture)).
- See also: T82, T1310

### T1334 Pre-register the prediction
`find` `prove` `bound` `compute` · stage: practice
aka: preregistration, registered reports, p-hacking, HARKing, refutation criteria, expected outcome, analysis plan
- What: writes down the expected outcome, the analysis and what would count as refutation before the run, so the story cannot be fitted to the result afterwards.
- Fits when: any experiment whose outcome could be rationalized either way (a search that "almost" finds, a fit that "roughly" matches).
- Lean: —
- Example: preregistration and registered reports, introduced against p-hacking and HARKing ([Wikipedia: Preregistration (science)](https://en.wikipedia.org/wiki/Preregistration_%28science%29)).
- See also: T1319, T1338
