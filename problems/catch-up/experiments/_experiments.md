# Experiments

| ID | Experiment | Tests | Outcome |
|---|---|---|---|
| [E1](E1.md) | Catch-Up values, N = 1..31 | C1 | {1..N}, N ≤ 31: a draw exactly at even totals; for even totals from N = 12, every opening draws |
| [E2](E2.md) | Catch-Up outcomes, N = 27..32 | C1 | N = 27–32 on the CPU engine: same as E1 for 27–31; N = 32 a draw, every opening draws |
| [E3](E3.md) | Catch-Up values, N = 32..35 | C1 | N = 32–35: 32 and 35 draw (every opening); 33 and 34 player-1 wins, only by opening 1 and 2; 33–35 unchecked |
| [E4](E4.md) | Entry into a provable high-phase class, N ≤ 24 | — | D forces entry into Hyb2T's exact class for N ≤ 24 (the debt part always); every describable subclass fails a few steps later (C23's class at 19, s4 at 23) |
| [E5](E5.md) | Hyb2 on all high sets, offsets within {0..15} | — | Hyb2 gives up a draw at about 6% of the ~1M high positions (offsets within {0..15}), smallest {0,2,3,4} at d = 1: not a universal high-phase strategy |
| [E6](E6.md) | Lead regime R2 | — | R2 (opponent trails by ≤ 2m − 1, ≤ 3 picks): D draws every even-total {1..N}, N ≤ 24, and every block p ≤ 9, a ≤ 40 except {2,3,4,5} and {1..6}; every fixed turn rule fails at N = 3 or 4 |
| [E7](E7.md) | Lead regimes with short turns | — | One-pick opponent turns fail at almost every block; two-pick turns for both (cap 2m − 1) draw blocks p ≤ 9 except a = 1 at p = 8, 9, and {1..N} as player 1 but not as player 2 from N = 15; fixed rules fail at N = 3, 4 |
| [E8](E8.md) | Hyb2 as the high phase on {1..N}, N ≤ 24 | — | With free low play, Hyb2 takes over at min ≥ span without losing the draw for every even-total N ≤ 24; switching earlier (min ≥ 2/3·span) fails from N = 16 |
| [E9](E9.md) | Bottom picks while the set is low, N ≤ 24 | — | D restricted to its k smallest numbers while low (min < c·span) fails within N ≤ 24 unless k is large for c: k = 6 holds for every c tested, k = 2 only at c = 1/2; the first failure moves later as k grows |
| [E10](E10.md) | Two-pick turns on {1..N}, N ≤ 24 | — | Two-pick turns for both (exact cap) draw every even-total {1..N}, N ≤ 24, in both roles; holding the opponent to one-pick turns fails from N = 7 |
| [E11](E11.md) | Two-ended menus on blocks, p = 9, 10 | — | Menus of the 3 smallest and 3 largest fail on blocks at p = 9 (a = 12) and p = 10 (a = 13–15), only as mover; a menu of 4 holds at p = 10, a ∈ [p, 2p] |
| [E12](E12.md) | Two-ended menus on {1..N}, N ≤ 24 | — | A defender choosing among the 3 smallest and 3 largest left draws every even-total {1..N}, N ≤ 24, in both roles; menus of 1 and 2 fail |
| [E13](E13.md) | Two-pick turns on blocks at heights 1 and 2, p ≤ 13 | — | With the exact cap (sum of the 2 smallest), D draws every block p ≤ 13 at heights 1 and 2 in both roles with ≤ 2 picks per turn; the cap 2m − 1 fails at a = 1 from p = 8 |
| [E14](E14.md) | C29's family in the two-pick class, N ≤ 28 | C29 | D draws {2..N} at deficit 1 in both roles for every even-total N ≤ 28 with ≤ 2 picks per turn: Catch-Up on {1..N} is drawn by two-pick play after the opening 1 |
| [E15](E15.md) | {3..N} at deficit 1 in the two-pick class, N ≤ 28 | — | D draws {3..N} at deficit 1 in both roles for every N ≤ 28 of the right parity (N ≥ 4) with ≤ 2 picks per turn; with E14, both starts of C31 (b) hold to N = 28 |
| [E16](E16.md) | Far 4-blocks act on margins by ψ^k (C34, position form) | C34 | m(S ∪ E_k, d) = ψ^k(m(S, d)) with 0 failures: k = 1 on S ⊆ {1..14}, k = 2 on S ⊆ {1..10} |
| [E17](E17.md) | Gap bound (C37) on every subset of {1..22} | C37 | No violation of C37's gap bound in 96,468,992 positions (every S ⊆ {1..22}, d ≤ 22); tight at ties exactly at {1..9}, {1..10}, {1..14}, {1..18}, {2, 4, …, 18} and kin |
| [E18](E18.md) | Least window of smallest numbers before Hyb2, N ≤ 24 | — | The least window of smallest numbers before Hyb2 grows with N: up to 12 at N = 24 when Hyb2 takes over at min ≥ span, about 6 (N/4) when it takes over at min ≥ 4·span; no fixed window works for every N ≤ 24 |
| [E19](E19.md) | Sliding the top quadruple of {1..N} (C35), N ≤ 20 | C35 | Sliding the top quadruple by any integer c leaves every even-total N ≤ 20 a draw (exact sweep, no non-draw) |
| [E20](E20.md) | Pairing bound (C60) on every subset of {1..22} and on multisets | C60 | No violation in 96,468,992 set positions (S ⊆ {1..22}, d ≤ 22) and 1,830,519 multiset positions; sharper than C37 at 38% of positions |
| [E21](E21.md) | Dense sets {1..N} minus at most 3 holes, N = 9..25 | C5, CU-L003 | No mover loss in 189,922 positions (every d ≤ N of draw parity): CU-L003 holds for N = 9..25; C5's 10 three-hole exceptions are all mover wins |
| [E22](E22.md) | Partially collapsed blocks, p ≤ 10, c ≤ 2p (C85) | C85 | Every t, every c = 1..2p, p ≤ 10: a draw at deficit \|t\| mod 2; I16 survives kill test (a) |
| [E23](E23.md) | Rank-perturbed intervals, random members at L = 23–26 (C84) | C84 | About 100 random members at each L = 23..26, no non-draw |
| [E24](E24.md) | Z strategies in the rounds game on collapsed blocks | C85 | First pick the highest bumped top, answers Hyb2: draws every t in both roles, p ≤ 9; (c) draws |
| [E25](E25.md) | Safe first turns in C83's boundary cases, N = 11..24 | C83 | No loss to N = 28; at N = 27, 28 every first turn of the defender is safe |
| [E26](E26.md) | C85's row form, p ≤ 10, c ≤ 2p | C85 | The band fails on collapsed blocks: diagonal non-draws, and off-diagonal from p = 7 |
| [E27](E27.md) | The draw band of blocks at every height, and on aligned dense pair sets | C86, C87 | Band holds at every integer height, p ≤ 10 (only (2, 2, 2)); aligned pair sets draw to N = 24 |
| [E28](E28.md) | How low can a block keep the rounds structure | C88 | Down to a ≈ (3p − 1)/2 only, never to 1 |
| [E29](E29.md) | Pair-deleted sets below half their size | C89 | Three losses inside C89's range, first at N = 19 |
| [E30](E30.md) | Round starts reached by E24's rule | C85 | Z starts: d ≤ c(R), at most one orphan pair; pre-switch Y: at most two |
| [E31](E31.md) | Simple Z rules under the one-pick cap | C86 | No Hyb2 variant goes below 2p − 1; the optimum ≈ 3p/2 is not a local rule |
| [E32](E32.md) | Collapsed blocks under the one-pick cap | C85 | One-pick play needs height ≈ 4p − 8 (blocks: ≈ 3p/2); the real game draws far lower |
| [E33](E33.md) | The lower ray's other forms | C91, C92 | Both hold at every even-total N from 11 to 28; fail only at N = 7, 8 |
| [E34](E34.md) | Tied odd blocks minus one number, every height (C105) | C105 | k ≤ 9 at every a ≤ 2(2k + 1) and a = (2k + 1)²: every draw-parity hole draws; \|m\| ≤ 1 at every hole |
| [E35](E35.md) | Tied blocks minus one number, every height (C106) | C106 | n ≤ 19: no loss at the draw parity; at a = 1 every {1..n} ∖ {h} of even total draws |
| [E36](E36.md) | The low column of blocks (C104) | C104 | n = 6..20, a ≤ n/2: every draw-parity d ≤ n − 1 draws, \|m\| ≤ 1; the column runs to the block's maximum from n = 12 |
| [E37](E37.md) | Tied odd blocks minus one number at every real height (C109) | C109 | k ≤ 7: every draw-parity hole draws on all of (0, ∞), exactly |
| [E38](E38.md) | The one-hole band (C110) | C110 | k = 3..9, every height tested, every hole: every draw-parity d ≤ k − 1 draws; the band ends exactly at d = k |
