# Rigorous numerics and computer-assisted analysis
Enclosures with proved error bounds: interval and ball arithmetic, Newton-type existence tests, validated integration and spectra.

### T64 Ball and interval arithmetic
`bound` `prove` `compute` · stage: enclose · signals: analytic, inequality, numeric-only
aka: Arb, FLINT, mpmath, ball arithmetic, interval arithmetic, high-precision arithmetic, enclosures, special functions, zeta function, de Bruijn–Newman constant
- What: each value is an enclosure [m ± r] that is guaranteed to contain the true result.
- Fits when: rigorous evaluation of special functions and zeta.
- Lean: for small instances, redo the computation with rational intervals in the kernel (T121).
- Example: the de Bruijn–Newman constant Λ ≤ 0.22, from explicit estimates plus numerics ([Polymath 15](https://arxiv.org/abs/1904.12438); [Arb](https://flintlib.org/doc/arb/index.html)).
- See also: T66, T67, T71, T124

### T65 Validated ODE integration
`prove` · stage: enclose · signals: dynamics, analytic
aka: interval integration of flows, directed rounding, rigorous enclosures, Lorenz attractor, Smale's 14th problem, periodic orbits, inequalities on boxes
- What: directed rounding and partitioning give rigorous enclosures of flows.
- Fits when: dynamics (attractors, periodic orbits) and inequalities on boxes.
- Lean: rational intervals are fine; ODE enclosures need a validated integrator, which Mathlib lacks (it has Picard–Lindelöf existence) and Isabelle has.
- Example: the Lorenz equations have a strange attractor, Smale's 14th problem ([Tucker](https://reliable-computing.org/tucker02.html)); the computational part was later verified in Isabelle/HOL ([Immler](https://www.mathematics.pitt.edu/node/3291)).
- See also: T64, T73

### T66 Verified interval arithmetic inside Lean
`bound` · stage: lean-tooling · signals: analytic, inequality, numeric-only
aka: girving/interval, girving/ray-render, software floating point, Int64 mantissa, conservative rounding, Mandelbrot set area, Koebe quarter theorem
- What: interval arithmetic on software floats (Int64 mantissa, UInt64 exponent) with Lean proofs that every operation is conservative.
- Fits when: box-heavy numerics done in Lean, where a soundness theorem for an algorithm is the goal.
- Lean: the generic soundness theorem counts; a concrete value needs evaluation by `decide +kernel` or `rfl`, out of reach at this depth; check `#print axioms` (T127).
- Example: ray-render proves in Lean that `upper_area d n` bounds the Mandelbrot set's area for every depth; the value ≈1.8265 at d = 12 comes from 99 minutes of compiled execution, not from the kernel ([girving/render](https://reservoir.lean-lang.org/@girving/render)).
- See also: T64, T120, T127

### T67 Interval Newton method
`find` `prove` · stage: enclose · signals: analytic, polynomial, numeric-only
aka: interval Newton, existence and uniqueness of a root, verified roots, nonlinear systems, box contraction
- What: one interval Newton step that maps a box into itself proves a unique zero in the box.
- Fits when: an approximate root of a nonlinear system must become a proved one.
- Lean: —
- Example: the interval Newton method ([Wikipedia: Interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic)).
- See also: T64, T68, T69

### T68 Newton–Kantorovich and radii polynomials
`find` `prove` · stage: enclose · signals: analytic, pde, dynamics, numeric-only
aka: Kantorovich theorem, radii polynomial method, contraction mapping, a posteriori validation, Chebyshev series, periodic orbits, homoclinic orbits, suspension bridge equation
- What: bounds on the residual and on the derivative near a numerical solution give a ball on which a Newton-like operator contracts, hence a true solution inside.
- Fits when: periodic orbits, homoclinics, special PDE solutions; the inequalities are rational and finitely many.
- Lean: a Lean 4 framework for the radii-polynomial method exists (its kernel-only status not checked); the inequalities are rational and finitely many.
- Example: homoclinic orbits of the suspension-bridge equation by radii polynomials and Chebyshev series ([arXiv:1702.07412](https://arxiv.org/abs/1702.07412)); a Lean 4 framework for the radii-polynomial method ([arXiv:2610.02335](https://arxiv.org/abs/2610.02335)); the theorem ([Wikipedia: Kantorovich theorem](https://en.wikipedia.org/wiki/Kantorovich_theorem)).
- See also: T67, T69, T72, T75

### T69 Certified homotopy continuation
`find` `compute` · stage: enclose · signals: polynomial, exact-value, numeric-only
aka: HomotopyContinuation.jl, alphaCertified, Smale's α-theory, numerical algebraic geometry, polynomial systems, counting real solutions, algebraic witnesses
- What: homotopy continuation tracks all roots; Smale's α-theory certifies Newton convergence, optionally in exact ℚ.
- Fits when: counting or locating solutions; algebraic witnesses for find problems.
- Lean: the α-test is cheap rational arithmetic; formalize the α-theorem or Kantorovich (T68) once.
- Example: alphaCertified certifies solutions of square systems, and that they are real ([Hauenstein–Sottile](https://arxiv.org/abs/1011.1091); [HomotopyContinuation.jl](https://www.juliahomotopycontinuation.org/)).
- See also: T59, T67, T68

### T70 Taylor-mode automatic differentiation
`prove` · stage: enclose · signals: analytic
aka: automatic differentiation, truncated Taylor arithmetic, generalized dual numbers, high-order derivatives, derivative bounds
- What: computes exact high-order derivatives of evaluated code by truncated Taylor arithmetic, for enclosures and Newton steps.
- Fits when: interval methods need derivative bounds of long formulas.
- Lean: —
- Example: truncated Taylor polynomial arithmetic on generalized dual numbers ([Wikipedia: Automatic differentiation](https://en.wikipedia.org/wiki/Automatic_differentiation)).
- See also: T64, T67

### T71 Rigorous quadrature
`compute` `bound` · stage: enclose · signals: analytic, inequality
aka: ball-arithmetic integration, Petras algorithm, adaptive Gauss quadrature, explicit constants, integrals with error bounds
- What: adaptive Gauss quadrature with proved error bounds for analytic integrands.
- Fits when: an explicit constant is an integral (explicit number theory, explicit bounds).
- Lean: —
- Example: Arb's integrator via the Petras algorithm ([arXiv:1802.07942](https://arxiv.org/abs/1802.07942)).
- See also: T64

### T72 Rigorous eigenvalue enclosures
`bound` `prove` · stage: enclose · signals: matrix, analytic, inequality
aka: Rayleigh–Ritz, Courant–Fischer, min-max theorem, spectral gaps, eigenpair enclosures, interval matrices, stability of linearizations
- What: trial subspaces give upper bounds (Rayleigh–Ritz, Courant–Fischer); contraction arguments enclose full eigenpairs.
- Fits when: spectral gaps, eigenvalue inequalities, stability of linearizations.
- Lean: —
- Example: Castelli–Lessard enclose eigendecompositions of interval matrices by radii polynomials ([arXiv:1112.5052](https://arxiv.org/abs/1112.5052); [Wikipedia: Rayleigh–Ritz method](https://en.wikipedia.org/wiki/Rayleigh%E2%80%93Ritz_method); [Wikipedia: Min-max theorem](https://en.wikipedia.org/wiki/Min-max_theorem)).
- See also: T68

### T73 Conley index and computational homology
`prove` · stage: enclose · signals: dynamics, topology
aka: Conley index, isolating neighbourhoods, cubical homology, cubical covers, chaos, invariant sets, Lorenz equations
- What: computes an algebraic-topological index of an isolating neighbourhood from a finite cubical cover; a nonzero index proves invariant sets or chaos.
- Fits when: global dynamics where pointwise enclosures are too fine.
- Lean: —
- Example: Mischaikow–Mrozek's computer-assisted proof of chaos in the Lorenz equations ([arXiv:math/9501230](https://arxiv.org/abs/math/9501230); [Wikipedia: Conley index theory](https://en.wikipedia.org/wiki/Conley_index_theory)).
- See also: T65, T82

### T74 Rigorous zero verification
`compute` `prove` · stage: enclose · signals: analytic, arithmetic-geometry
aka: Riemann hypothesis verification, zeros of the zeta function, RH up to height T, explicit number theory
- What: interval-arithmetic location of zeta zeros.
- Fits when: explicit results that need RH up to a height T.
- Lean: not checkable here; usable only as an explicit hypothesis.
- Example: RH verified up to height 3·10¹² ([Platt–Trudgian](https://arxiv.org/abs/2004.09765)).
- See also: T64

### T75 Computer-assisted PDE proofs
`prove` · stage: enclose · signals: pde, numeric-only
aka: finite-time blowup, Euler equations, Boussinesq equations, special solutions, approximate solution plus stability estimates
- What: an approximate solution plus rigorous stability estimates.
- Fits when: blow-up and existence of special solutions.
- Lean: beyond current tooling.
- Example: finite-time blowup of 2D Boussinesq and 3D axisymmetric Euler with boundary ([Chen–Hou](https://arxiv.org/abs/2210.07191)).
- See also: T68, T72
