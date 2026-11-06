# Understanding

**Holds.**
- Gordon's table has 70,543 rows (`instances.csv`); He–Wu's four obstructions and three
  constructions leave 22,459 open (README, reproduced by the importer). On 2026-11-06 the table
  is 86.86% settled, 9,266 open (journal).
- Every `none` rule so far is local: one quotient H, one prime p, a congruence modulus
  (p^(e/2) from self-conjugacy C5/C13/C14/C23, Ma's lemma C21, the Sylow trace C22, the
  character rules C17/C19/C20) or a multiplier orbit structure (C9/C10 for every n, I13; the
  orbit search I5; coset sums A7) against the coefficient range 2c, c = v/|H|. Each is one
  Lean theorem plus one kernel check over its rows; all are classical in idea (Turyn, Ma,
  McFarland/Gordon Thm 5.1, Miller), new in SDS form and in Lean.
- The element of order 2 splits an SDS (C26, I21): when 4 ∣ n on a quotient C_{2^j} × K (2 self-conjugate mod exp K),
  Ma's step makes D(x) ≡ D(x + u) mod 2, so D = P·Z + (1 − u)·T with Z an SDS-like vector (v/2, (k + λ)/4, λ/2) on G/P
  and T a weighing element of weight n/4 (twisted when j ≥ 2). Both halves are smaller questions: a parity condition
  kills 177 rows, a `none` halved row kills 112 more (C26 at c = 1), and conversely a known halved set plus a weighing
  matrix inside its zeros builds new sets (O79–O84 for six open rows).
- A rule's edge is a rich source: C22 at p = 2 with equality, C21 at equality (I20) and
  self-conjugate primes inside the multiplier group (C25, I18) each reach rows the plain
  rule misses.
- "Open" often means "never searched" or "the database lags": orbit and exhaustive
  searches found sets for open rows (E4, E7, E10, O34–O38), published Paley-type sets were
  never entered (O71–O78), and the cyclotomic and Singer constructions of ideator round 3
  give ten more (O61–O70, I19). Every proposed row is first checked against Gordon,
  He–Chen–Ge and He–Wu.
- Kernel and machine are the bottleneck, not ideas, for about 2,500 rows: kernel memory is
  per declaration, so large checks are split into slices (`SetCheckSplit`,
  `cosetSearch_of_slices`); Lean runs one process at a time, and a part of A7's rows takes
  about 8 min (state.md, Running).
**Blocks.** The open rows split by what is missing (ideator round 3 core reports, main
folder `scratch/ideator/2026-11-06-core-{none,exists}.md`):
- search power: rows with gcd(v, n) = 1 whose orbit search was cut (core B1/B2, about
  1,450); I17's mod-q split reaches only r ≲ 27 orbits as prototyped;
- a reduction at a rule's edge: about 1,800 near-misses (core A, Ma at equality; margins in
  [½, 1));
- constructions: p-groups with n a power of p (core D1, 350; the twins of X1's sets);
- the core K, about 3,100 rows: no usable multiplier (gcd(v, n) > 1, or tiny M), every
  congruence modulus below c, quotient vectors exist on every quotient E8 decides, and far
  below the random threshold. They are probably `none`, but no local view can show it.
**So a Solution must.** Per row: a set Lean checks, or a rule's Lean theorem plus its
Lean check for that row; and, before it is proposed, a check against the known
constructions of Gordon, He–Chen–Ge and He–Wu. For the core K, a rule that reads the
{0, ±1} values on G itself (several quotients or primes at once, or the lift from a quotient
to G as in I16), with a certificate the kernel can check.
