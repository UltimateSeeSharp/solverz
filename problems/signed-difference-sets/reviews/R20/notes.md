# C21 refuter running notes (2026-11-06)

## Proof sketch, step by step (paper check)
- A = Z[H]/(P) = Z[K][x]/(Phi_{p^j}(x)) = Z[K] (x) Z[zeta]: P = Phi_{p^j}(g) since Phi_{p^j}(X) = sum_{t<p} X^{t p^{j-1}}; H-sum = (sum K)(sum C_{p^j}) and sum C_{p^j} = P * (sum_{t<p^{j-1}} g^t), so H -> 0. OK.
- pi^phi = p*u with u a unit of Z[zeta] (subring of A) => holds in A. OK.
- pi non-zero-divisor: A free over the domain Z[zeta] with basis K, pi acts coordinatewise. OK.
- A/piA = Z[K] (x) Z[zeta]/(1-zeta) = F_p[K]. Involution: pibar = -x^{-1} pi so piA is stable; induced map on F_p[K] is k -> -k. OK.
- Frobenius: y^{p^i} = sum a_k (p^i k) in F_p[K]; p^i = -1 mod exp K gives y^{p^i} = ybar. F_p[K] semisimple (p !| |K|) so reduced. OK.
- Induction: Y_t Ybar_t = w * pi^{e*phi - 2t} * n' (w unit, n' = n/p^e); while exponent >= 1, pi | Y_t. Ends with Y in pi^{ceil(e*phi/2)} A, and ceil(e*phi/2) >= floor(e/2)*phi, so Y in p^b A. p=2, j=1: phi=1, pi=2, A=Z[K]; same. OK.
- Final: Y = p^b X1 + P X2 in Z[H]; (1-g_P)P = 0 so (1-g_P)Y in p^b Z[H]; |a_h - a_{h-g_P}| <= 2c < p^b => equal => Y = P*Z -> 0 in A, but n != 0 in A (A free Z-module, 1 part of a basis). OK, needs n != 0 (n = 0 only for the trivial k = lambda = v set).
- (Corrected, see frob.py) The condition p^i = -1 mod exp K is exactly what the step needs: exp K is itself an element order, so 'self-conjugate mod every element order' is the same condition; e.g. p = 2, K = C3 x C5 (2 self-conj mod 3 and mod 5, not mod 15) has 30 nonzero y in F_2[K] with y*ybar = 0.

## Row list (independent: rows.py, witness.py, compare.py)
- rows.py: own parser of instances.csv (70,543 rows), best H per p (j = max p-exponent, K = largest p'-quotient of exponent m over all m with p self-conj mod m). Rule fires on 4,607 rows: 3,124 `none`, 1,483 `open`, 0 `exists`. No row has n <= 0.
- compare.py: all 1,241 ma_hits ids are in my hits; my hits inside rest.txt = 1,241, so the two lists are equal on rest.txt. All 1,241 are still `open` in instances.csv. 242 further `open` rows are hit that were outside rest.txt (removed earlier by B1-B3), so C21 also covers them.
- witness.py: every ma_hits line's data equals its instances.csv row and its (p, j, K) meets the hypotheses (p prime, e >= 2, j <= p-exponent of G, K a quotient of G's p'-part by primary-exponent domination, p self-conj mod exp K, p^b > 2c): 0 bad. Tightest margin p^b/2c = 1.0625 (N47010).

## Known sets (objtest.py, objtest.out)
- 102 concrete sets (objects/O1-O39, E10 `found`, E4/E7 `yes` in r4.out/e7.out, B4's 12 order-64 sets) re-verified as SDS by my own autocorrelation: 102/102.
- On every quotient shape C_{p^j} x K meeting C21's hypotheses (p | n with e >= 2, all j, all p'-quotients K up to iso, |H| <= 3000; 6 random surjections each): 954 tests of the lemma (1 - g_P)Y = 0 mod p^b, 0 violations; the rule p^b > 2c fires on none of the 102 sets. (E11 has no `found` line.) O3 (CW(4,4) in C4) sits at p^b = 2c = 2: the strict inequality is needed.

## Brute force on autocorrelation (brute.py, brute_a.out)
- Every Y in [-r, r]^H with constant off-zero autocorrelation, n = Y Ybar(0) - mu, e >= 2: (1 - g_P)Y = 0 mod p^b checked.
  C2 x C3 r=4 (444 Y with b=1, 180 with b=2, 36 with b=3), C4 x C3 r=1 (144), C2 x C5 r=1 (100), C8 r=3 (480 b=1, 192 b=2), C3 x C2 r=4 (336): 0 violations; n = 0 cases constant on P-cosets. C5 x C2, C3 x C4, C3 x C2 x C2 at r=1 had no Y with e >= 2.
- Control C2 x C7 (2 not self-conj mod 7): 56 violations, e.g. n = 4, Y = a CW(7,4) inside the coset {0} x C7. The self-conjugacy hypothesis is needed and the test has teeth.

## Weakest steps, exhaustively (frob.py / frob.out, norm.py)
- Every y in F_p[K]: ybar == y^(p^i) (Frobenius matches the induced involution) and y*ybar = 0 => y = 0, for 17 claim cases (p = 2: K = C3, C5, C9, C3^2, C11, C13; p = 3: C2, C4, C2^2, C5, C7, C2xC4, C10; p = 5: C3, C6, C2^2; p = 7: C4, C2^2): 0 mismatches, 0 zero divisors of that form. Controls where p is not self-conj mod exp K: p=2 K=C7 (14), C15 (30), C3xC5 (30); p=3 K=C8 (16); p=5 K=C4 (8); p=7 K=C3 (12) nonzero y with y*ybar = 0. So the hypothesis is the right one and is needed.
- pi^phi = p*u, u a unit of Z[zeta_{p^j}] (hence of A, which contains Z[zeta] as a subring with the same 1): (1-x)^phi mod Phi_{p^j} has all coefficients divisible by p and N(u) = 1 exactly (determinant of multiplication by u) for p^j in {2,4,8,16,32,3,9,27,5,25,7,49,11,13}. (A first floating-point norm gave 11.45 for 27 and 245.9 for 25: cancellation, not a counterexample.)

## Algebraic core in A directly (algtest.py, alg_a.out, alg_b.out)
- Every alpha in A with coordinates in [-r, r] on the Z-basis {g^t k: t < phi} and alpha*alphabar = n in A (weaker than constant autocorrelation): alpha in p^b A, and alpha = 0 when n = 0. Batch a (p = 2: K = C3 r=8 incl. b = 2, 3; C5, C9, C3^2, C11, C13; j = 2, 3 with K = C3, C5; K = 1 with j = 2 r=20 up to b = 4, j = 3 r=6): 0 violations. Control p=2 K=C7 r=2: 84 violations (n = 16, b = 2 among them).
- Batch b (p = 3: K = C2 r=6 (112 with b=1), C4, C2^2, C5, C7, j=2 K=1 (24 with b=1), j=2 K=C2; p = 5: K = 1 (12), C2, C3; p = 7: K = C2): 0 violations. Odd p with K != 1 and e >= 2 is thin in small boxes (only p=3, K=C2); the exhaustive F_p[K] check above is the real test of that step.

## Counts (ideator's numbers)
- Re-derived: by p 3: 572, 2: 216, 5: 191, 7: 165, 11: 70, 13: 21, 17: 3, 19: 3; 691 cyclic / 550 not; v < 100: 52, 100-199: 196, >= 200: 993; rows killed with K = 1 alone: 269. All match B5.

## Exhaustive searches vs smallest hits
- N75 (27,17,8) C27: E4 `no` (r4.out). N140 (32,28,12) C32: E4 `no`. N168, N176 (36,.,.) C2 x C18: E7 `no` (e7.out) and contraction KILL. N133 (32,20,4) C32: E7 `cut` at 1e10 nodes (no information). No hit row has a `yes`/`found` line anywhere.

## Proof: odd e and p = 2, j = 1
- p = 2, j = 1: phi = 1, pi = 2, A = Z[K] with involution k -> -k; e odd is then impossible (the last division gives pi | n'), matching He-Wu Thm 3.2; the claim's conclusion holds vacuously there. For Lean, inducting only up to t = b*phi keeps the exponent e*phi - 2t >= 2 at every step (no half step needed).
- Statement reading: 'for some i' with i = 0 adds nothing (exp K = 2 only for p odd, where i = 1 works too); 'K = 1 or' is redundant (mod 1 everything is -1). e >= 2 forces n != 0 (padicValNat 0 = 0 in Lean). n > 0 on every row (|lambda| <= k).
- objtest2.out coverage of the 954 real-set tests: p=2 K=1 b=1..5 (666), p=2 K>1 b=1 (36), p=3 K=1 b=1 (126), p=3 K>1 b=1 (60), p=5 (30), p=7 (36).
- tensor.py / tensor.out: tensor products of CW(4,4), CW(6,4), CW(7,4), CW(8,4) (lambda = 0 is closed under products), each verified: CW(36,16) C6xC6, CW(24,16) C4xC6, CW(42,16) C6xC7, CW(96,64) C4xC4xC6, CW(216,64) C6^3, CW(48,16) C6xC8, CW(168,64) C4xC6xC7: 64 quotient tests (43 with K != 1, b = 2 or 3), 0 violations, rule never fires.

## Literature (opened)
- Tan, Group Invariant Weighing Matrices (arXiv 1610.01914, ar5iv): Ma's lemma as Result 2.7 (cyclic Sylow p, chi(Y) = 0 mod p^a for nontrivial chi => Y = p^a X1 + P X2; Ma, PhD thesis HKU 1985) and Turyn's self-conjugacy as Result 2.6; used separately for CW nonexistence.
- Arasu-Gordon-Zhang, New Nonexistence Results on CW (arXiv 1908.08447): Lander/Turyn self-conjugacy only (Thm 2.1); no Ma.
- Gordon, Signed Difference Sets (arXiv 2212.10630 v1): no nonexistence theorems beyond integrality and lambda >= -1; no Ma, Turyn.
- He-Wu, Nonexistence results and constructions for SDS (arXiv 2608.22936 v2, 2026-09-20): four obstructions (self-conj prime: v_p(n) even; C2-quotient; two parity ones); Ma's lemma not used, Ma cited only for a PDS survey.
- Gordon, Cyclic RDS and CW (arXiv 2501.14924 v2): Lam's self-conjugacy bound for RDS only.
- AJC vol. 18 p. 111 (OCR, authors not readable): a CW argument deriving 'P - N = p^b X1 + Q X2' (Q of order p), citing Ma's thesis: the same Ma + self-conjugacy move on CW.
- Not opened: Pott 1995 (LNM 1601) section 1.5; Arasu-Ma 2001 (EMIS returned 503); Ma-Schmidt McFarland PDF (binary).
