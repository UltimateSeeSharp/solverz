# Sliding the top quadruple of {1..N} (L35), N ≤ 20

Does V({1..N−4} ∪ ({N−3..N} + c), 0) depend on the shift c? `Solver` at every integer c from 0 to T(N) + 1, T(N) = 1 + … + N; every comparison is j·c + b with |j| ≤ 4, |b| ≤ T(N), so the value is constant beyond T(N) and the sweep is exact for integer c.

- Date: 2026-10-28
- Command: `slide_quad 20` (`./target/release/slide_quad.exe`)
- Commit: fd6e756
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: 65 s
- Checked: control first, O19's base {5, 6, 7} with {8..11} + c: Draw, Draw, Win, Win at c = 0..3, as known; independently, the refuter's engine found the same for every integer c, N ≤ 20, and every real c, N ≤ 16 (log 2026-10-28: Const survives the refuter)
- Scope completed: every even-total N from 4 to 20. A run for N = 23 alone (`slide_quad 23 23`, commit 66b43bc) was cut at 15 minutes without output.
- Data: `scratch/slide_quad-20.txt`, SHA-256 `5827ece7fbdde36969d640be74b97fdfbe8cfb9a94ccce5f7d24064919a8f508`

## Outcome

| N | shifts c | non-draws |
|---|---|---|
| 4 | 0..11 | none |
| 7 | 0..29 | none |
| 8 | 0..37 | none |
| 11 | 0..67 | none |
| 12 | 0..79 | none |
| 15 | 0..121 | none |
| 16 | 0..137 | none |
| 19 | 0..191 | none |
| 20 | 0..211 | none |
