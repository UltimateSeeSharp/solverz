# Understanding

**Holds.**
- Gordon's table has 70,543 rows (`instances.csv`); He–Wu's four obstructions and three
  constructions leave 22,450 open (README, reproduced by the importer).
- Most open rows fall to rules on the parameters alone, each proved on paper and
  refuter-checked, none in Lean yet: self-conjugacy on quotients (C5, C6, C7; I3)
  7,682 rows, multipliers with an orbit exhaust (C9, C10; I5) 4,088 + 232, support parity
  (C8; I4) 553, contraction searches (C3, C4; I6) 132. Together 12,302 of the 22,450
  (exploration counts, rechecked independently by the refuters): the table would go from
  68.2% to 85.6% settled. The rules are classical (Turyn 1965, McFarland/Gordon Thm 5.1,
  the weighing-matrix parity bound), newly applied to the table.
- "Open" often means "never searched": exhaustive and orbit searches found sets for 16 of
  the 41 open rows with v ≤ 40 they finished (E4, E7) and for N286, N352, N638 (I9).
- Partial difference sets with λ′ − μ = 2 give SDSs (C11): 8 open rows so far (I7), and a
  negative Latin square family beyond the table with members m = 3–6 (C12, I8).
- "Open" is not enough for a Solution: the database lags the papers (12 rows a published
  construction settles, refuter db-lags) and some of its labels lack a valid witness
  (state.md, Needs the user). Every proposed row is first checked against Gordon, He–Chen–Ge
  and He–Wu.
- A found set is cheap to certify: `decide` checks v = 27 in about 40 s, the bit-mask
  `checkSet` v = 361 in 77 s (`solver/answer.py`).
- The kernel keeps every reduction of one declaration, about 0.1 MB per search node, so
  per-row searches above 5·10⁴ nodes must be split across declarations, and Lean modules
  build one at a time (state.md, Resources).
**Blocks.** Nothing counts until Lean checks it. The rules need their Lean theorems: C5
for j = 1 is elementary (Frobenius in F_p[H]); C9 is elementary only for squarefree n, so
I5's 1,602 rows with non-squarefree n need cyclotomic ideals in Lean. Per-row searches
(I5's orbit exhaust, I6) cost kernel time and memory. About 10,100 open rows (mostly
v ≥ 200) have no method yet.
**So a Solution must.** Per row: a set Lean checks, or a rule's Lean theorem plus its
Lean check for that row; and, before it is proposed, a check against the known
constructions of Gordon, He–Chen–Ge and He–Wu.
