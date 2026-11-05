# Signed difference sets solver

Import (`import/`, Python): `import.py` writes `instances.csv` from Gordon's
`sds.json` and He–Wu's obstructions; `settle.py` writes our answers into it.

## Engines
| Engine | What | Checked against |
|---|---|---|
| P1 exhaustive (`src/lib.rs`, `search`) | every SDS of one case, 0 marked, sign sum +s | known sets O1–O5 and three more found (E1); the triage Python search agrees on N3, N32; E4 repeats E1's node counts |
| P2 cyclotomic (`src/cyclotomic.rs`, `search`) | every SDS on (GF(q), +) constant on the classes of order e and on 0 | every sign choice for q ≤ 200 agrees with `is_sds`; the Paley sets, Lehmer's (73, 9, 1), O6's (25, 12, 1) (E6) |
