# Signed difference sets solver

Import (`import/`, Python): `import.py` writes `instances.csv` from Gordon's
`sds.json` and He–Wu's obstructions; `settle.py` writes our answers into it.

## Engines
| Engine | What | Checked against |
|---|---|---|
| P1 exhaustive (`src/lib.rs`, `search`) | every SDS of one case, 0 marked, sign sum +s | known sets O1–O5 and three more found (R1); the triage Python search agrees on N3, N32 |
