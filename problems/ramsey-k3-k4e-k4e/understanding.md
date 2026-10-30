# Understanding

**Holds.**
- Known: 21 ≤ R ≤ 22 (README). Valid 20-point colourings exist (O1, Lean
  `paper20_valid`; 40 block-circulant ones over ℤ₁₀ with 2 rings, R4); O1
  has no 21st point (F1), and neither has any of those 40 (R4, the deepest
  partial row colours 19 of 20 pairs).
- The 2012 construction split a (J₇, K₃)-good graph; R(K₃, J₇) = 21 means
  no such graph exists on 21 points, so an answer's colours 1 ∪ 2 contain
  J₇ and it is built differently (README, arXiv:1201.0554).
- Symmetry: no valid K₂₁ colouring is invariant under a fixed-point-free
  permutation of order 7 (P2, R2), which covers both Cayley families (P1,
  P5). The largest valid circulant has 15 points (R1); block-circulants are
  plentiful at 15 and 18 points (R2's engine). Untrusted: the refuter's
  SAT runs find order-7 symmetries with fixed points UNSAT too.
- Engines: annealing reaches valid colourings at 16–19 points but stalls at
  3 violations at 20 (R5 tuning); CaDiCaL 2.1.2 ships with the Lean toolchain.

**Blocks.** Every structured family tried at 21 points is empty, and
annealing cannot even reach the known 20-point colourings.

**So a solution must.** Be a 21-point colouring with no colour-keeping
symmetry of order 7, not containing O1, whose colours 1 ∪ 2 contain J₇.
The evidence leans mildly towards none existing; the unrestricted SAT
search (P4) is the decisive test of the first goal.
