# Understanding

**Holds.**
- Gordon's table has 70,543 cases (`instances.csv`): 146 exist, 2,574 are
  ruled out by his searches, which covered cyclic groups; tiny non-cyclic
  cases stay Open, their cyclic twins "No, Orbit Exhaust" (README).
- He–Wu's four obstructions rule out 45,361 of the 67,823 Open cases on
  paper, and their constructions settle 3; 22,459 stay open (README,
  reproduced by the importer).
- Exhaustive search with one element fixed (P1, F1, F2) takes seconds at
  small v (R1); contraction to a quotient (F3) gives small certificates. N3
  fell to the first, N32 to both, each proved in Lean.
**Blocks.** Non-existence counts only with a Lean proof. Exhaustion by
`decide` reaches about 3⁸ patterns in 5 minutes; contraction needs a checked
search over integer vectors once the vector space is large. Cases near
k ≈ v/2 at v ≥ 27 are beyond plain P1.
**So a solution must.** Per Instance: a set Lean checks, or a Lean proof that
none exists (exhaustion after F2, or F3 with a checked vector search).
