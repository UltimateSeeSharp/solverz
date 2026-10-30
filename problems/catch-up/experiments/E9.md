# Bottom picks while the set is low, N ≤ 24

Can a defender D draw {1..N} (even totals, both roles, perfect opponent) if it picks only among its k smallest numbers left while the set is low, min < c·span (span = max − min), and freely once it is high (B35)?

- Date: 2026-10-26
- Command: `low_high 24 <k> <num> <den> 0` for k ∈ {1, 2, 3, 4, 6} and c = num/den ∈ {1/2, 2/3, 1, 3/2, 2} (`./target/release/low_high`)
- Commit: 1885660
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: under 3 s per run
- Checked: unrestricted (k = 30) every even-total N ≤ 20 draws. An independent script (`scratch/b35/low_high.py`) gives the same failures for N ≤ 12 at (k, c) = (1, 1/2), (2, 1), (2, 1/2), (3, 1), (4, 1), (3, 2/3).
- Data: `scratch/low_high/grid-24-free.txt`, SHA-256 `0c7dfb1b60bd0ca062956ea0feb79d434e44dbfdfe13c33dd2ac07e4081c0b09`

## Outcome

First failing N for each pair (k, c); "—" means D draws every even-total N ≤ 24 in both roles.

| k \ c | 1/2 | 2/3 | 1 | 3/2 | 2 |
|---|---|---|---|---|---|
| 1 | 8 | 8 | 7 | 4 | 4 |
| 2 | — | 23 | 11 | 7 | 7 |
| 3 | — | — | 19 | 12 | 12 |
| 4 | — | — | — | 23 | 19 |
| 6 | — | — | — | — | — |

With the top 3 numbers only once high (k = 3, c = 1, `low_high 24 3 1 1 3`) D fails from N = 15.
