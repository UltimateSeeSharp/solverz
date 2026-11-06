# Claims

| ID | Claim | Uses | Status | Lean | Approved |
|---|---|---|---|---|---|
| [C1](C1.md) | Square condition: k + λ(v − 1) = s², and the signs sum to ±s (every Instance) | — | open | — | — |
| [C2](C2.md) | Translation and negation keep an SDS an SDS (every Instance) | — | verified | `IsSDS.translate`, `IsSDS.neg` | — |
| [C3](C3.md) | Contraction: coset sums along G → H have autocorrelation λ times the fibre size (every Instance) | — | verified | `IsSDS.contract_autocorr`, `abs_contract_le` | — |
| [C4](C4.md) | Coset sums: Σ \|a\| ≤ k with the same parity; fibres of a surjection have \|G\|/\|H\| elements (every Instance) | C3 | open (Lean proof, refuter pending) | `IsSDS.sum_abs_contract_le`, `IsSDS.sum_abs_contract_parity`, `card_fibre_eq` | — |
