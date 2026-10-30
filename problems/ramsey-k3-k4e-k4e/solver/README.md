# R(K₃, K₄−e, K₄−e) solver

## Engines
| Engine | What | Checked against |
|---|---|---|
| `violations` | colour-0 triangles plus 4-point sets with a K₄−e in colour 1 or 2; 0 iff Lean's `Valid` | O1 scores 0, broken copies score above 0 (`cargo test`); independent Python checks of O1 |
| `extensions` | every one-point extension of a valid colouring | O1 has none and O1 minus any point has exactly two, its own among them, as the refuter's independent scripts found |
