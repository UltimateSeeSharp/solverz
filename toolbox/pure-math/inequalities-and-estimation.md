# Inequalities and estimation
Classical inequalities and the working tricks of estimation: convexity, Cauchy–Schwarz, Hölder, majorization, geometric and functional inequalities, dyadic pigeonholing, amplification, tensor powers.

### T605 AM–GM, Jensen and convexity
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: arithmetic–geometric mean inequality, Jensen's inequality, convex functions, weighted means, power means, tangent line trick, equality cases, olympiad inequalities
- What: compare averages of convex functions; equality cases guide the proof.
- Fits when: symmetric inequalities; optimization with product or sum constraints.
- Lean: Mathlib: `Real.geom_mean_le_arith_mean_weighted`, `ConvexOn.map_sum_le`; closing steps by `nlinarith`, `positivity` (T128).
- Example: AM–GM by Jensen's inequality for log ([Wikipedia: Jensen's inequality](https://en.wikipedia.org/wiki/Jensen's_inequality), [Wikipedia: AM–GM](https://en.wikipedia.org/wiki/Inequality_of_arithmetic_and_geometric_means)).
- See also: T608, T609, T128

### T606 Cauchy–Schwarz as a decoupling tool
`prove` `bound` · stage: argue · signals: analytic, graph, inequality
aka: Cauchy–Schwarz inequality, decoupling a variable, counting 4-cycles, Kővári–Sós–Turán, large sieve, removing a variable from a sum, second moment
- What: separate a bilinear expression into two quadratic ones, each easier to control.
- Fits when: counting 4-cycles, large-sieve-type bounds, removing a variable from a sum.
- Lean: Mathlib: `Finset.sum_mul_sq_le_sq_mul_sq`, `norm_inner_le_norm`.
- Example: counting 4-cycles in graphs; large-sieve instances ([Tricki: How to use the Cauchy–Schwarz inequality](https://www.tricki.org/article/How_to_use_the_Cauchy-Schwarz_inequality)).
- See also: T607, T621, T373

### T607 Hölder (geometric view)
`prove` `bound` · stage: argue · signals: analytic, inequality, product-structure
aka: Hölder's inequality, L^p norms, multilinear bounds, generalized Hölder, volume of a box, interpolation of norms
- What: interpolate between L^p norms; view the inequality as the volume of a box.
- Fits when: products of several functions; multilinear bounds.
- Lean: Mathlib: `Real.inner_le_Lp_mul_Lq` (finite sums), `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`.
- Example: the Tricki's geometric proof ([Tricki: Geometric view of Hölder's inequality](https://www.tricki.org/article/Geometric_view_of_H%C3%B6lders_inequality)).
- See also: T606, T612, T635

### T608 Majorization and Schur-convexity (Karamata, Muirhead)
`prove` · stage: argue · signals: analytic, order, inequality, symmetric
aka: majorization order, Karamata's inequality, Muirhead's inequality, Schur-convex functions, symmetric sums with exponents, doubly stochastic matrices
- What: a symmetric convex function respects the majorization order.
- Fits when: symmetric sums with exponents; comparing spread-out and concentrated vectors.
- Lean: — (Karamata, Muirhead and Schur-convexity not found in Mathlib); a fixed instance by `nlinarith` or an SOS certificate (T54).
- Example: Karamata's inequality ([Wikipedia: Karamata's inequality](https://en.wikipedia.org/wiki/Karamata's_inequality), [Wikipedia: Schur-convex function](https://en.wikipedia.org/wiki/Schur-convex_function)).
- See also: T605, T609, T657

### T609 Rearrangement inequality
`prove` · stage: argue · signals: order, inequality
aka: similarly ordered sequences, Chebyshev's sum inequality, monovarying functions, cyclic sums, permutations of a sum
- What: similarly ordered sequences maximize Σ a_i b_i.
- Fits when: cyclic or ordered sums.
- Lean: Mathlib: `MonovaryOn.sum_smul_comp_perm_le_sum_smul`, Chebyshev's `MonovaryOn.sum_mul_sum_le_card_mul_sum`.
- Example: the rearrangement inequality and its proofs of AM–GM and Chebyshev's sum inequality ([Wikipedia: Rearrangement inequality](https://en.wikipedia.org/wiki/Rearrangement_inequality)).
- See also: T605, T608

### T610 Lagrange multipliers and boundary analysis
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: Lagrange multipliers, critical points, constrained optimization, KKT, extreme value theorem, boundary cases, few-variable optimization
- What: locate extrema at critical points or on the boundary.
- Fits when: smooth constrained optimization in few variables.
- Lean: Mathlib: `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, `IsCompact.exists_isMinOn`.
- Example: method of Lagrange multipliers ([Wikipedia: Lagrange multiplier](https://en.wikipedia.org/wiki/Lagrange_multiplier)).
- See also: T51, T22

### T611 Brunn–Minkowski and Prékopa–Leindler
`prove` `bound` · stage: argue · signals: geometry, analytic, inequality
aka: Brunn–Minkowski inequality, Prékopa–Leindler, log-concave functions, Minkowski sum, concavity of volume, isoperimetric inequality, Borell–Brascamp–Lieb
- What: volume is concave under Minkowski addition; the functional form holds for log-concave functions.
- Fits when: isoperimetric-type and convex-geometric inequalities.
- Lean: — (Brunn–Minkowski and Prékopa–Leindler not found in Mathlib).
- Example: the isoperimetric inequality from Brunn–Minkowski ([Wikipedia: Brunn–Minkowski theorem](https://en.wikipedia.org/wiki/Brunn–Minkowski_theorem), [Wikipedia: Prékopa–Leindler inequality](https://en.wikipedia.org/wiki/Prékopa–Leindler_inequality)).
- See also: T613, T746, T798

### T612 Projection inequalities (Loomis–Whitney, Brascamp–Lieb)
`prove` `bound` · stage: argue · signals: geometry, analytic, inequality, product-structure
aka: Loomis–Whitney inequality, Brascamp–Lieb inequality, multilinear integrals, counting by coordinate projections, box theorem, Finner's inequality
- What: bound a set or an integral by its projections.
- Fits when: counting by coordinates, multilinear integrals.
- Lean: — (Loomis–Whitney and Brascamp–Lieb not found by name; Mathlib's Gagliardo–Nirenberg–Sobolev proof in `Analysis/FunctionalSpaces/SobolevInequality.lean` uses a Loomis–Whitney-type grid-line argument).
- Example: Loomis–Whitney inequality; Brascamp–Lieb ([Wikipedia: Loomis–Whitney inequality](https://en.wikipedia.org/wiki/Loomis–Whitney_inequality), [Wikipedia: Brascamp–Lieb inequality](https://en.wikipedia.org/wiki/Brascamp–Lieb_inequality)); Shearer's entropy version is T364.
- See also: T364, T607, T615

### T613 Symmetrization (Steiner, rearrangements)
`prove` `bound` · stage: argue · signals: geometry, analytic, inequality, symmetric
aka: Steiner symmetrization, symmetric decreasing rearrangement, Riesz rearrangement inequality, Pólya–Szegő, isoperimetric problems, radial optimizers, ball is extremal
- What: replace a set or function by a more symmetric one that improves the functional.
- Fits when: extremal problems whose optimizer should be a ball or a radial function.
- Lean: — (Steiner symmetrization and Riesz rearrangement not found in Mathlib).
- Example: Steiner's symmetrization proof of the isoperimetric inequality; Riesz rearrangement ([Wikipedia: Steiner symmetrization](https://en.wikipedia.org/wiki/Steiner_symmetrization), [Wikipedia: Riesz rearrangement inequality](https://en.wikipedia.org/wiki/Riesz_rearrangement_inequality), [Wikipedia: Isoperimetric inequality](https://en.wikipedia.org/wiki/Isoperimetric_inequality)).
- See also: T611, T350, T681

### T614 Hardy-type inequalities
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: Hardy's inequality, averaging operators, weighted inequalities, Carleman's inequality, discrete Hardy inequality, integral operators
- What: weighted averages are bounded by the function.
- Fits when: integral operators of averaging type.
- Lean: — (Hardy's inequality not found in Mathlib).
- Example: Hardy's inequality ([Wikipedia: Hardy's inequality](https://en.wikipedia.org/wiki/Hardy's_inequality)).
- See also: T634, T615

### T615 Functional inequalities (Poincaré, Sobolev, log-Sobolev)
`prove` `bound` · stage: argue · signals: analytic, pde, inequality, random
aka: Poincaré inequality, Sobolev inequality, Gagliardo–Nirenberg, log-Sobolev inequality, Gross, spectral gap, mixing rates, concentration
- What: control a function by its gradient.
- Fits when: concentration, mixing rates, PDE estimates.
- Lean: Mathlib: `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` (Gagliardo–Nirenberg–Sobolev); Poincaré and log-Sobolev inequalities not found.
- Example: Gross's log-Sobolev inequality ([Wikipedia: Logarithmic Sobolev inequalities](https://en.wikipedia.org/wiki/Logarithmic_Sobolev_inequalities), [Wikipedia: Poincaré inequality](https://en.wikipedia.org/wiki/Poincaré_inequality), [Wikipedia: Sobolev inequality](https://en.wikipedia.org/wiki/Sobolev_inequality)).
- See also: T778, T779, T695

### T616 Polynomial inequalities (Markov, Bernstein, Remez, Chebyshev extremality)
`prove` `bound` · stage: argue · signals: polynomial, analytic, inequality
aka: Markov brothers' inequality, Bernstein's inequality, Remez inequality, Chebyshev polynomials, extremal polynomials, sup norms, approximation theory
- What: bound derivatives or sup norms of polynomials by their size on sets.
- Fits when: polynomials of bounded degree on intervals; approximation theory.
- Lean: Mathlib has `Polynomial.Chebyshev.T`; Markov and Remez inequalities not found.
- Example: Markov brothers' inequality, extremal at Chebyshev polynomials ([Wikipedia: Markov brothers' inequality](https://en.wikipedia.org/wiki/Markov_brothers'_inequality), [Wikipedia: Chebyshev polynomials](https://en.wikipedia.org/wiki/Chebyshev_polynomials), [Wikipedia: Remez inequality](https://en.wikipedia.org/wiki/Remez_inequality)).
- See also: T617, T649

### T617 Equioscillation
`prove` · stage: argue · signals: polynomial, analytic, inequality
aka: Chebyshev alternation theorem, best uniform approximation, minimax polynomials, Remez algorithm, extremal polynomials, optimality certificate
- What: a best uniform approximation is characterized by alternating maximal errors.
- Fits when: proving optimality of an approximation or an extremal polynomial.
- Lean: — (equioscillation not found in Mathlib); the alternation points of a given approximant are a finite check.
- Example: Chebyshev's equioscillation theorem ([Wikipedia: Equioscillation theorem](https://en.wikipedia.org/wiki/Equioscillation_theorem)).
- See also: T616, T649

### T618 Grothendieck's inequality
`bound` · stage: argue · signals: matrix, inequality, graph
aka: Grothendieck constant, cut norm, SDP rounding, bilinear forms over unit vectors versus signs, MaxCut approximation, quadratic programming over ±1
- What: bilinear forms over unit vectors are within a constant of those over signs.
- Fits when: rounding SDP relaxations; cut norms.
- Lean: — (not found in Mathlib).
- Example: Grothendieck's inequality and the cut norm ([Wikipedia: Grothendieck inequality](https://en.wikipedia.org/wiki/Grothendieck_inequality)).
- See also: T53, T352

### T619 Square and rearrange
`prove` `compute` · stage: argue · signals: analytic, integers, exact-value
aka: square the sum, expand into a double sum, change variables, differentiate the phase, Gaussian integral, Gauss sums, |G|² = p, large sieve
- What: square a sum, expand into a double sum, change variables to differentiate the phase.
- Fits when: exponential sums, Gaussian integrals, large sieve.
- Lean: Mathlib: `integral_gaussian`, `gaussSum_sq`, `gaussSum_mul_gaussSum_eq_card`.
- Example: computing ∫e^{−x²} and evaluating Gauss sums ([Tricki: Square and rearrange](https://www.tricki.org/article/Square_and_rearrange)).
- See also: T482, T530, T606

### T620 Dyadic pigeonholing
`prove` `bound` · stage: argue · signals: analytic, inequality
aka: dyadic decomposition, dyadic scales, Cauchy condensation, pigeonholing over scales, log loss, popular scale, Erdős similarity problem
- What: split a range into O(log) dyadic scales and keep the scale carrying the most mass, at the cost of a log factor.
- Fits when: a sum or integral mixes many magnitudes and a log loss is affordable.
- Lean: Mathlib: Cauchy condensation `NNReal.summable_condensed_iff`.
- Example: Bourgain's argument on the Erdős similarity problem, dissected by Tao; Cauchy condensation as the textbook case ([arXiv:2009.06736](https://arxiv.org/abs/2009.06736), [Tricki: Dyadic decomposition](https://www.tricki.org/article/Dyadic_decomposition)).
- See also: T325, T632, T625

### T621 Amplification (arbitrage of symmetry)
`prove` `bound` · stage: argue · signals: analytic, inequality, symmetric
aka: arbitrage, exploit a symmetry one side lacks, scaling, translation, modulation, optimize free parameters, dimensional analysis, Sobolev exponents
- What: apply a weak estimate to transformed copies (scaled, translated, modulated) and optimize the free parameters.
- Fits when: one side of an inequality has a symmetry the other side lacks.
- Lean: a hand proof; the optimized inequality closes by `nlinarith` or `positivity` (T128).
- Example: the textbook Cauchy–Schwarz proof by scaling; dimensional analysis showing when Sobolev embeddings must fail ([Tao: amplification and the tensor power trick](https://terrytao.wordpress.com/2007/09/05/amplification-arbitrage-and-the-tensor-power-trick/)).
- See also: T622, T624, T606

### T622 Tensor power trick
`prove` `bound` · stage: argue · signals: analytic, inequality, product-structure
aka: tensor power, n-fold product, take n-th roots, remove constants, remove logarithms, Hardy–Littlewood majorant conjecture, Plünnecke–Ruzsa amplification
- What: apply the inequality to the n-fold product, take n-th roots and let n → ∞ to delete constants and even logarithms.
- Fits when: the quantities are multiplicative under products and a bound holds with a lossy constant.
- Lean: a hand proof; the final n → ∞ limit by hand.
- Example: disproof of the Hardy–Littlewood majorant conjecture; Ruzsa's amplification of Plünnecke's inequality ([Tricki: The tensor power trick](https://www.tricki.org/article/The_tensor_power_trick), [Tao: amplification](https://terrytao.wordpress.com/2007/09/05/amplification-arbitrage-and-the-tensor-power-trick/)).
- See also: T621, T416, T646

### T623 Create an epsilon of room
`prove` · stage: argue · signals: analytic, inequality
aka: ε of room, perturb then let ε → 0, approximation by smooth functions, strictly subharmonic perturbation, Riemann–Lebesgue lemma, maximum principle
- What: prove a version with a loss ε (or for a perturbed object), then let ε → 0.
- Fits when: the exact statement is fragile but stable under small perturbations.
- Lean: a hand proof; Mathlib: Riemann–Lebesgue `tendsto_integral_exp_inner_smul_cocompact`.
- Example: the Riemann–Lebesgue lemma by approximation; the maximum principle via a small strictly subharmonic perturbation ([Tricki: Create an epsilon of room](https://www.tricki.org/article/Create_an_epsilon_of_room)).
- See also: T631, T645, T671

### T624 Keep parameters free, optimize at the end
`prove` `bound` · stage: argue · signals: inequality
aka: free parameters, choose the threshold last, balance two errors, optimize λ, cutoff selection, small and large cases
- What: carry thresholds and cutoffs symbolically and fix them once all error terms are visible.
- Fits when: an argument splits into small and large cases or trades two errors against each other.
- Lean: a hand proof; the final optimized inequality by `nlinarith` or `positivity` (T128).
- Example: Cauchy–Schwarz by optimizing λ in Σ(a − λb)² ≥ 0 ([Tricki: keep parameters unspecified](https://www.tricki.org/article/Keep_parameters_unspecified_until_it_is_clear_how_to_optimize_them)).
- See also: T621, T128

### T625 Interchange the order of summation
`prove` `compute` · stage: argue · signals: analytic, integers, identity
aka: swap sums, Fubini, double counting for sums, orthogonality relations, character sums, Gelfand's pushforward, Poincaré–Hopf
- What: swap sums or integrals so the inner one becomes a count, an orthogonality relation or a character sum.
- Fits when: a double sum or integral appears and one variable is easier to sum first.
- Lean: Mathlib: `Finset.sum_comm`, `MeasureTheory.integral_integral_swap`.
- Example: the top answer of MathOverflow's "few tricks" thread, with Gelfand's pushforward version that yields Poincaré–Hopf ([MO: few tricks](https://mathoverflow.net/questions/363119/every-mathematician-has-only-a-few-tricks)).
- See also: T327, T479, T715

### T626 Treat approximations as exact; neglect lower-order terms
`prove` · stage: practice · signals: analytic, asymptotic
aka: leading-order heuristic, main term first, top-order energy estimates, first approximation, error bookkeeping later
- What: run the argument with the main term only to see whether it works, then handle errors.
- Fits when: an expression has a clear leading term and the risk is drowning in error bookkeeping.
- Lean: —
- Example: energy estimates for nonlinear PDE that keep only the top-order terms first ([Tricki: neglect lower order terms](https://www.tricki.org/article/As_a_first_approximation_neglect_lower_order_terms), [Tricki: use an approximation as if exact](https://www.tricki.org/article/Use_an_approximation_as_if_it_were_exact)).
- See also: T624, T670
