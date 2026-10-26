# Two-ended menus on {1..N}, N ≤ 24

Does a defender D who picks only among the k smallest and k largest numbers left (menu tb_k) still draw Catch-Up on {1..N}, even totals, as player 1 and as player 2, against a perfect opponent (B35)? D's minimax final margin; D fails if it is negative in either role.

- Date: 2026-10-26
- Command: `two_ended_intervals 24 1`; `two_ended_intervals 24 2`; `two_ended_intervals 24 3` (`cargo run --release -p catch-up --bin two_ended_intervals -- …`)
- Commit: 69ca3a5
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: tb3 2 min 34 s (N = 24 needs 2 GB); tb1, tb2 under 3 min together
- Checked: the menu logic is that of `two_ended_blocks` (reproduces the ideator's engine); on {1..N} tb2 fails first at N = 19, as the ideator's independent engine (`scratch/ideator/review2/menus*.rs`) found.
- Data: `scratch/b35/two_ended_intervals-24-{1,2,3}.txt`, SHA-256 `a8aeae7b302f61de180ebfe36c172180f7cc7490ba6c46396bbdcd328d17a59f`, `9235bb01392eee9ccb67d84fe43ac0e196ecb2357517ec7e86a563761189684b`, `fb5a833435a332b5a18c41cbf2ef6665137955e84f843ab0c10c126fd5ce537a`

## Outcome

| menu | D fails at (even totals N ≤ 24) | margins there |
|---|---|---|
| tb1 (smallest or largest) | N = 7, 8, 11, 12, 15, 16, 19, 20, 23, 24 | −2 as player 1 (and as player 2 from N = 8) |
| tb2 | N = 19, 20, 23, 24 | −2 in both roles |
| tb3 | none | |

So a defender choosing among the 3 smallest and 3 largest numbers left draws {1..N} in both roles for every even total N ≤ 24.
