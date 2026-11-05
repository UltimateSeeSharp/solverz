# Understanding

**Holds.** Gordon's table leaves tiny non-cyclic cases Open because his
searches covered cyclic groups only (README). Exhaustive search with one
element fixed (P1, F1, F2) takes seconds at small v and found none for S1 and
S2 (triage, to be rerun as a recorded run). He–Wu's obstructions removed two
thirds of the open cases by theory, leaving about 22,460 (README).
**Blocks.** Non-existence counts only with a Lean proof: plain exhaustion by
`decide` reaches v ≈ 12; larger cases need the symmetry facts (F1, F2) and
quotient arguments proved, and a checked search that uses them.
**So a solution must.** Per case: a set Lean checks, or a Lean proof that none
exists.
