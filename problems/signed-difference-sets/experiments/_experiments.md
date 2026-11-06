# Experiments

| ID | Experiment | Tests | Outcome |
|---|---|---|---|
| [E1](E1.md) | I1 engine, exhaustive | I1 on N3, N32 | exhausted both (rechecked by the triage script; both proved in Lean) |
| [E4](E4.md) | I1 engine to the first set | I1 on open, v ≤ 40 (53) | inconclusive, stopped at 31 of 53: 15 found (6 Lean-checked), 16 exhausted (no Lean proof) |
| [E5](E5.md) | Contraction engine, open v ≤ 40 | C3 on open, v ≤ 40 | 12 killed (Lean rechecks: `Answer/N<id>`), 34 not decided |
| [E6](E6.md) | I2 engine, every q ≡ 1 mod 8 up to 10⁵ | I2 on q ≤ 10⁵ | found: O12 for N35840 (Lean-checked); otherwise sporadic sets, none for another open Instance |
| [E7](E7.md) | I1 engine to the first set, E4's unreached Instances | I1 on 22 open, v ≤ 40 | suspended at 11 of 22: N131 found (O13, Lean pending), 9 exhausted, N133 cut |
| [E10](E10.md) | Orbit exhaust (C9 multipliers), open with gcd(v, n) = 1 | I5 (A5) on 12,209 open | stopped at 8,626 (all ≤ 50 orbits): 7,762 none, 14 found (O34–O38 new), 850 cut |
| [E11](E11.md) | Orbit exhaust, E10's remaining rows, cap 10⁵ | I5 (A5) on 3,583 open | 110 none, 3,473 cut |
