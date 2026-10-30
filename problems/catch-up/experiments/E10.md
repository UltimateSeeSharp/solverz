# Two-pick turns on {1..N}, N ≤ 24

Can a defender D draw {1..N} (even totals, both roles, perfect opponent) while every turn of both players is at most 2 picks (B31, B41)? D takes at most 2 picks per turn and ends each turn with the opponent behind by at most the sum of the 2 smallest numbers left, or by more than everything left (then the opponent has lost); so whatever the opponent picks, it catches up within 2 picks. D with no allowed turn loses.

- Date: 2026-10-26
- Command: `turn_cap intervals 24 2 2` (`./target/release/turn_cap`)
- Commit: 9a27538 (the run used the build just before the optional menu argument was added; with no menu the code path is the same)
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: about 5 min (N = 24 needs about 2.5 GB)
- Checked: unrestricted (`turn_cap intervals 16 30 30`) every even-total N ≤ 16 draws, and blocks p ≤ 5, a ≤ 12 draw, as known. An independent script written from the rules (`scratch/turn_cap/check.py`) gives the same outcomes for N ≤ 12.
- Data: `scratch/turn_cap/turn_cap-intervals-24-2-2.txt`, SHA-256 `83c1309e9842f9d7e53c6d1bbfe5aedc5c61e897e76562e2ab2d906d5ed118e2`

## Outcome

D draws every even-total N ≤ 24 in both roles. With the opponent held to one-pick turns (cap: the smallest number left) D fails from N = 7 as player 2 and from N = 8 in both roles (`check.py 2 1 12`, N ≤ 12 only). In `check.py` (N ≤ 12) the class still draws with the stricter cap 2m − 1 (m the smallest number left), and with D also restricted to the 3 smallest or 3 largest numbers; with the 2 smallest or 2 largest it fails at N = 11, 12 as player 2 (`turn_cap intervals 12 2 2 2` agrees).

This replaces the intervals table of [lead-regime-short-turns.md](lead-regime-short-turns.md), whose engine refused turns that win outright (fixed in 49a7676).
