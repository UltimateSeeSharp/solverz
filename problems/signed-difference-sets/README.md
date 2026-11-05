# Signed difference sets

Settle open cases of Gordon's signed difference set table, circulant weighing
matrices included. Now: [state.md](state.md).

## Problem
A signed difference set (SDS) with parameters (v, k, λ) in a finite abelian
group G of order v: k elements of G, each marked + or −, such that every
non-identity element g is hit by the differences (x + g) − x of marked
elements with total sign λ (the sum of D(x)·D(x + g) over x). In group-ring
terms D D⁻¹ = (k − λ) + λG. Special cases: all signs + is an ordinary
difference set; λ = 0 in a cyclic group is a circulant weighing matrix
CW(v, k). Every case of Gordon's table (a group with parameters) is an
Instance in [instances.csv](instances.csv), keyed `SDS(v,k,λ,[invariant
factors])`; G is the product of `ZMod` over the factors.
**Goal:** for each open Instance, `HasSDS G k λ` (Lean checks the set) or
`¬ HasSDS G k λ`; Lean `SignedDifferenceSets.HasSDS` in
`lean/SignedDifferenceSets/Statement.lean`, pending the user's approval.
Kind: find, many Instances, both goals open.
Estimate: small cases are exhaustive or SAT searches of seconds to hours on
this machine; a found set is a v-entry sign vector that Lean checks by
`decide` in seconds. Non-existence counts only with a Lean proof: plain
exhaustion (one element fixed, `decide`) reaches v ≈ 12; beyond that it needs
facts (quotient and character arguments) proved in Lean.

## Literature
- Gordon, Signed difference sets, Designs, Codes and Cryptography
  ([arXiv:2212.10630](https://arxiv.org/abs/2212.10630), 2022): defines SDSs,
  generalizing difference sets and circulant weighing matrices, with existence
  results. Database [dmgordo/signed-difference-sets](https://github.com/dmgordo/signed-difference-sets)
  (`sds.json`, CC-BY-4.0): every group-specific case, Yes, No or Open. Its
  searches covered cyclic groups; tiny non-cyclic cases stay Open, e.g.
  (9, 8, 1) in C₃ × C₃. Imported 2026-11-05 at e3bf810 (2026-04-24): 70,543
  cases, 146 Yes or All, 2,574 No (Orbit Exhaust), 67,823 Open.
- He, Wu, Nonexistence results and constructions for signed difference sets
  ([arXiv:2608.22936](https://arxiv.org/abs/2608.22936), v2 2026-09-20): four
  obstructions (self-conjugate primes, C₂-quotient, near-full-support,
  small-defect) rule out 45,361 of the 67,823 open cases with 9 ≤ v ≤ 499;
  constructions settle 3 more ((64, 22, 6) in C₂⁶, (256, 106, 42) in C₂⁸,
  (125, 28, 3) in C₅³). About 22,460 stay open; their script
  ([zhiwenhe94/sds-open-case-verification](https://github.com/zhiwenhe94/sds-open-case-verification))
  writes the remaining list. No computer search of the remaining cases.
  Read 2026-11-05 at de57332; `solver/import/import.py` applies the same four
  tests and the three constructions, and reproduces their counts: 45,361
  ruled out, 22,459 open.
- Circulant weighing matrices: Arasu, Gordon, Zhang 2021
  ([arXiv:1908.08447](https://arxiv.org/abs/1908.08447), Table 10: 22 open
  CW(n, k), n ≤ 200, k ≤ 100); Tan 2026
  ([arXiv:2608.18468](https://arxiv.org/abs/2608.18468)) rules out 8, leaving
  14 (k = 36: n = 112, 117, 180, 195; k = 81: 156, 195, 198; k = 100: 112,
  120, 155, 156, 165, 182, 195), all expected not to exist.
- Searched 2026-11-05 (arXiv, the web, the AI-contribution lists in
  problems.md): no other work on the open SDS cases, no AI attention.
