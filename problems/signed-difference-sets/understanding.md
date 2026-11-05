# Understanding

**Holds.**
- Gordon's table leaves small non-cyclic cases Open because his searches
  covered cyclic groups only (README); their cyclic twins are "No, Orbit
  Exhaust". He–Wu's four criteria remove two thirds of the open cases by
  theory, about 22,460 stay open (README); reimplemented on the 91 Open keys
  with v ≤ 40, they leave 55 (`scratch/hewu.py`, agrees with the paper's
  examples).
- Two cheap tools settle small cases: exhaustive search with one element
  fixed (P1, F1, F2), seconds at v ≤ 20 (R1); and contraction to a quotient
  (F3), which kills 13 of the 55 by a small integer-vector check
  (`scratch/contract2.py`). S1 fell to the first, S2 to both, each proved in
  Lean (cases.md).
**Blocks.** Non-existence counts only with a Lean proof. Exhaustion by
`decide` reaches 3⁸ patterns in about 5 minutes; the contraction kills need a
pruned vector check in Lean, since their plain vector spaces (up to 7⁸) are too
large for `decide`. Cases near k ≈ v/2 at v ≥ 27 are beyond plain P1.
**So a solution must.** Per case: a set Lean checks, or a Lean proof that none
exists (exhaustion after F2, or F3 with a checked vector search).
