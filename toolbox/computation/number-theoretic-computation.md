# Number-theoretic computation
Searches, sieves, factoring, lattice reduction and primality certificates for integers and Diophantine equations.

### T40 Structured Diophantine search
`find` · stage: search · signals: integers, construction
aka: sums of three cubes, x³+y³+z³=k, 33, 42, Diophantine equations, sieving, parametrization, Charity Engine
- What: sieving and parametrization make enormous ranges searchable, while the answer stays tiny.
- Fits when: find problems whose object is a few integers.
- Lean: `norm_num` checks the identity instantly; the ideal certificate.
- Example: x³+y³+z³=33 ([Booker](https://arxiv.org/abs/1903.04284)); 42 and 3, found on Charity Engine's volunteer grid of about 500k PCs ([Booker–Sutherland](https://arxiv.org/abs/2007.01209)).
- See also: T41, T118, T153

### T41 Search on a parametrized curve
`find` · stage: search · signals: arithmetic-geometry, integers, construction
aka: elliptic curves, rational points, Euler's sum of powers conjecture, Euler quartic conjecture, Elkies, Frye, a⁴+b⁴+c⁴=d⁴
- What: reduces the search to rational points on an elliptic curve.
- Fits when: equations with curve structure.
- Lean: `norm_num` on the identity.
- Example: Euler's quartic conjecture is false: Elkies found 2682440⁴+15365639⁴+18796760⁴=20615673⁴ (with infinitely many more), and Frye found the smallest, 422481 ([history](https://proofwiki.org/wiki/Euler_Quartic_Conjecture/Historical_Note)).
- See also: T40, T45

### T42 Segmented sieve verification up to a bound
`compute` `prove` · stage: search · signals: integers
aka: Goldbach verification, sieve of Eratosthenes, numerical verification, finite range check, checking every n ≤ N
- What: checks every n ≤ N.
- Fits when: evidence, or the finite part of a proof.
- Lean: evidence only at this scale.
- Example: even Goldbach checked to 4·10¹⁸ in 781.8 CPU-years ([Oliveira e Silva](https://sweet.ua.pt/tos/goldbach.html)).
- See also: T121, T152

### T43 Pratt/Lucas primality certificates
`prove` `compute` · stage: certify · signals: integers
aka: primality proof, Pratt certificate, Lucas test, Pocklington, Nat.Prime, large primes, primitive root witness
- What: a witness a with a^(p−1)=1 and a^((p−1)/q)≠1 for each prime q dividing p−1, applied recursively.
- Fits when: any proof that needs specific large primes.
- Lean: Mathlib's `lucas_primality` is a theorem, not a tactic: write the certificate recursion yourself, with `decide +kernel` on the `ZMod` power conditions (core `Nat.powMod`, square-and-multiply); `norm_num`'s trial division overflows the kernel beyond about 25 bits.
- Example: Mathlib's `lucas_primality`, "the basis of the Pratt primality certificate" ([LucasPrimality](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LucasPrimality.html)); `norm_num` stack overflow beyond 25 bits ([NormNum.Prime](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/NormNum/Prime.html)).
- See also: T44, T121, T125

### T44 Factoring engines
`compute` · stage: algebra · signals: integers, exact-value
aka: ECM, Lenstra elliptic-curve factorization, quadratic sieve, number field sieve, cyclotomic values, Fermat numbers, sequence terms
- What: ECM's run time depends on the smallest factor, so it peels medium factors off huge numbers; the factorization is trivially checkable.
- Fits when: compute problems needing factorizations (cyclotomic values, Fermat-type numbers, sequence terms).
- Lean: a factorization is checked by multiplication (`norm_num`); primality of the factors by T43.
- Example: the largest ECM factor so far has 83 digits ([Wikipedia: Lenstra elliptic-curve factorization](https://en.wikipedia.org/wiki/Lenstra_elliptic-curve_factorization)).
- See also: T43, T45

### T45 Number-theory CAS
`compute` · stage: algebra · signals: integers, arithmetic-geometry
aka: PARI/GP, Magma, Sage, class groups, elliptic curves, modular forms, L-functions, factorization, number fields
- What: class groups, elliptic curves, modular forms, L-functions and factorization out of the box.
- Fits when: any arithmetic object must be computed before it is certified.
- Lean: outputs are untrusted; certify each fact a proof uses.
- Example: PARI/GP ([PARI/GP](https://pari.math.u-bordeaux.fr/); [Wikipedia: PARI/GP](https://en.wikipedia.org/wiki/PARI/GP)).
- See also: T29, T44, T81

### T46 Lattice basis reduction (LLL)
`find` `prove` · stage: algebra · signals: integers, matrix, construction
aka: LLL, short lattice vectors, integer relations, Diophantine approximation, algebraic dependence, 0/1 solutions, Kramer–Mesner systems, Mertens conjecture
- What: short lattice vectors give small integer relations or 0/1 solutions.
- Fits when: Diophantine approximation, design existence, algebraic dependence.
- Lean: the found vector is checked exactly; analytic consequences need interval arithmetic.
- Example: the Mertens conjecture, disproved with zeta zeros and lattice reduction ([Odlyzko–te Riele](https://ir.cwi.nl/pub/6447/6447D.pdf)); Kramer–Mesner plus LLL found all 4,996,426 7-(33,8,10) designs with group PΓL(2,32) ([Wassermann](https://www.mat.univie.ac.at/~slc/wpapers/s35wasser.pdf)).
- See also: T27, T47, T76

### T47 Lattice enumeration and BKZ
`find` `compute` · stage: algebra · signals: geometry, matrix, exact-value
aka: BKZ, block reduction, Fincke–Pohst, lattice sieving, shortest vector problem, SVP, closest vector problem, CVP, lattice minimal vectors, kissing configurations
- What: block reduction plus enumeration or sieving find exact shortest or closest vectors, beyond LLL's approximation.
- Fits when: minimal vectors and kissing configurations of lattices, small integer solutions.
- Lean: a found vector is checked exactly; no Lean route for minimality in the sources.
- Example: BKZ, enumeration, sieving and Fincke–Pohst ([Wikipedia: Lattice problem](https://en.wikipedia.org/wiki/Lattice_problem)).
- See also: T46
