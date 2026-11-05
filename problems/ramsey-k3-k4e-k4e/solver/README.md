# R(K₃, K₄−e, K₄−e) solver

Import (`import/`, Python): `import.py` writes `instances.csv` (one Instance, N1).

## Engines
| Engine | What | Checked against |
|---|---|---|
| `violations` | colour-0 triangles plus 4-point sets with a K₄−e in colour 1 or 2; 0 iff Lean's `Valid` | O1 scores 0, broken copies score above 0 (`cargo test`); independent Python checks of O1 |
| `extensions` | every one-point extension of a valid colouring | O1 has none and O1 minus any point has exactly two, its own among them, as the refuter's independent scripts found |
| `block` | block-circulant colourings over ℤₘ with r rings, by backtracking over pair classes | equal counts to scoring every assignment with `violations` (m, rings) = (3, 3), (4, 3), (5, 2); the refuter's independent search and SAT (E2) |
| `anneal` | simulated annealing on `violations`, rescoring only sets through the changed pair | incremental score equals a full recount (`cargo test`); reaches valid colourings at 16–19 points, stalls at 20 |
| `sat` + `r6_sat` | CNF of `Valid` on Kₙ, cube-and-conquer over point 0's sorted row with CaDiCaL 2.1.2 (shipped with the Lean toolchain) | a colouring satisfies the clauses iff `violations` is 0 (`cargo test`); finds valid colourings at 12 and 16 points; every model rescored |
