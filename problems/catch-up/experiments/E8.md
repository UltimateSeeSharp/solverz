# Hyb2 as the high phase on {1..N}, N ≤ 24

Can a defender D draw {1..N} (even totals, both roles, perfect opponent) if it must play Hyb2 once the set is high, min ≥ c·span (span = max − min), and plays its k smallest numbers (k = 30: freely) before (A8)? Hyb2 here is memoryless: with an odd number of numbers left D answers with the smallest pick leaving the opponent behind by at least the matching cost of what is left (L20), else the largest; with an even number left it takes the largest.

- Date: 2026-10-26
- Command: `low_high 24 <k> <num> <den> h` for (k, c) = (30, 1), (30, 1/2), (30, 2/3), (30, 2), (8, 1), (12, 1) (`./target/release/low_high`)
- Commit: a8a9b7b
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: about 1–5 min per run (824 MB)
- Checked: unchecked beyond `low_high`'s own checks ([low-high-n24.md](low-high-n24.md)); the Hyb2 rule reproduces L24 on blocks in `hyb2_universal` (same rule, rounds game).
- Data: `scratch/a8/low_high-hyb2-24.txt`, SHA-256 `ca60d8005c275c8d64ffb907065102bb5e0d772b9c11ccfadf83f5beb30af1b8`

## Outcome

| low phase | switch to Hyb2 at | D fails at (even totals N ≤ 24) |
|---|---|---|
| free | min ≥ span | none |
| free | min ≥ 2·span | none |
| free | min ≥ (2/3)·span | 16, 19, 20, 23, 24 |
| free | min ≥ span/2 | every N from 7 |
| 12 smallest | min ≥ span | none |
| 8 smallest | min ≥ span | 23, 24 |

So Hyb2 can take over as soon as the set is high (min ≥ span, L24's regime) without losing the draw, for every N ≤ 24; switching earlier fails, as L24's tightness predicts.
