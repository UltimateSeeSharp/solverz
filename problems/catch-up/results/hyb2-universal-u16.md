# Hyb2 on all high sets, offsets within {0..15}

Is Hyb2 (L24's strategy) a drawing strategy on every high set, not only full blocks (A8's high phase)? In the rounds game (L13), for every even offset set O ⊆ {0..15} and every debt d ≤ sum(O) with d + sum(O) even (where a draw is possible), Z's guaranteed outcome with Hyb2 against a perfect Y versus the exact outcome, Z as mover and as the other.

- Date: 2026-10-26
- Command: `hyb2_universal 16 40` (`./target/release/hyb2_universal`)
- Commit: 1ff118b
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: 10 s
- Checked: full blocks {0..2p−1} at debt p mod 2, p ≤ 8, draw exactly and with Hyb2 in both roles, as L24 says; otherwise unchecked.
- Data: `scratch/a8/hyb2_universal-16.txt`, SHA-256 `02a97ccbba604c5a7207e5d8a7d39bf17d177e656f018793c440de2424c66f80`

## Outcome

1,007,615 positions. Hyb2 fails to secure a draw that Z could secure at 56,691 positions as mover and 58,429 as the other (about 6% each); it does worse than exact play (a win given up included) at 60,177 and 403,292. The smallest failures have a hole next to the bottom: O = {0, 2, 3, 4} at d = 1 (Z to move: exact draw, Hyb2 loses), O = {0, 3, 4, 5} at d = 0 (exact win, Hyb2 loses), O = {0, 2, 3, 5} at d = 2 (Z second: exact win, Hyb2 loses).

So Hyb2 is not a universal high-phase strategy: a low phase handing over to it must reach a narrower class.
