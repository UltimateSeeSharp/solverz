# Lead regimes with short turns

Can a defender D draw while every turn of both players stays short, against a perfect opponent (B41)? D must end each of its turns with the opponent trailing by at most a cap (m = the smallest number left) and may use at most a given number of picks per turn; D with no allowed turn loses.

- Date: 2026-10-26
- Command: `lead_regime blocks 9 40 1 1 0 2`; `… blocks 9 40 1 1 0 3`; `… blocks 9 40 2 1 -1 2`; `… intervals 24 2 1 -1 2` (`./target/release/lead_regime`)
- Commit: ac9fd30 (`lead_regime`, unchanged since)
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: 15 s, 15 s, 52 s, 45 s
- Checked: the engine matches `Solver` unrestricted (`lead_regime check`, see [lead-regime-r2.md](lead-regime-r2.md)); these runs unchecked otherwise.
- Data: `scratch/b41/lead_regime-blocks-9-40-1-1-0-2.txt` (SHA-256 `86ffeb8e0ad5cd62c46e7202cfb9ed3a23c55a2a7eeb44d1410a1d31491000e5`), `…-1-1-0-3.txt` (`9fa71b7b93da9803f41607eeda139c1b1ce15033560f3938fce269c9e7032aa1`), `…-2-1-m1-2.txt` (`d133476c6ad0f5d9939d32e5d9094574a00e640ffdf65f5db121dcd03766505a`), `lead_regime-intervals-24-2-1-m1-2.txt` (`38997d0f8acd8dca7c213eaa2a9b0489de6455c56b491718968b68262327b62a`)

## One-pick opponent turns (cap m), blocks, p ≤ 9, a ≤ 40

With D allowed 2 or 3 picks per turn, D fails at every height for every p ≥ 2 (p = 2, 3 as mover from a = 2, 3; p ≥ 4 in both roles at every a); p = 1 never fails. Keeping every opponent turn to one pick is impossible at any height.

## Two-pick turns for both (cap 2m − 1, D at most 2 picks)

Blocks {a..a+2p−1} at gap p mod 2, scope p = 1..9, a = 1..40. D fails only at: p = 2, a = 2 (as mover); p = 3–7 and 9, a = 1 (as the other player); p = 8, a = 1 (both roles). Every other block is a draw for D in both roles.

Intervals {1..N}, even totals N ≤ 24:

| N | D as player 1 | D as player 2 |
|---|---|---|
| 3, 4, 7 | D | D |
| 8, 11, 12, 15 | D | L |
| 16 | L | L |
| 19 | D | L |
| 20, 23, 24 | L | L |

With 3 picks for D (R2) every interval N ≤ 24 draws ([lead-regime-r2.md](lead-regime-r2.md)).
