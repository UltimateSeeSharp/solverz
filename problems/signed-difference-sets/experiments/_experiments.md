# Experiments

| ID | Experiment | Tests | Outcome |
|---|---|---|---|
| [E1](E1.md) | P1 engine, exhaustive | P1 on N3, N32 | exhausted both (rechecked by the triage script; both proved in Lean) |
| [E4](E4.md) | P1 engine to the first set | P1 on open, v ≤ 40 (53) | inconclusive, stopped at 31 of 53: 15 found (6 Lean-checked), 16 exhausted (no Lean proof) |
| [E6](E6.md) | P2 engine, every q ≡ 1 mod 8 up to 10⁵ | P2 on q ≤ 10⁵ | found: O12 for N35840 (Lean-checked); otherwise sporadic sets, none for another open Instance |
| [E7](E7.md) | P1 engine to the first set, E4's unreached Instances | P1 on 22 open, v ≤ 40 | running |
