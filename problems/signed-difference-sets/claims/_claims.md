# Claims

| ID | Claim | Uses | Status | Lean | Approved |
|---|---|---|---|---|---|
| [C1](C1.md) | Square condition: k + λ(v − 1) = s², and the signs sum to ±s (every Instance) | — | verified | `IsSDS.sum_sq` | — |
| [C2](C2.md) | Translation and negation keep an SDS an SDS (every Instance) | — | verified | `IsSDS.translate`, `IsSDS.neg` | — |
| [C3](C3.md) | Contraction: coset sums along G → H have autocorrelation λ times the fibre size (every Instance) | — | verified | `IsSDS.contract_autocorr`, `abs_contract_le` | — |
| [C4](C4.md) | Coset sums: Σ \|a\| ≤ k with the same parity; fibres of a surjection have \|G\|/\|H\| elements (every Instance) | C3 | open (Lean proof, refuter pending) | `IsSDS.sum_abs_contract_le`, `IsSDS.sum_abs_contract_parity`, `card_fibre_eq` | — |
| [C5](C5.md) | Rule SC: self-conjugacy congruence on a quotient | C3 | verified | `not_hasSDS_of_selfConj` | — |
| [C6](C6.md) | Rule SC++: residue class and moments | C1, C3, C5 | proved | — | — |
| [C7](C7.md) | Rule A2: marked counts per coset | C4, C6 | verified (LP form, 237 rows) | `not_hasSDS_of_marked` | — |
| [C8](C8.md) | Rule A3: support parity | — | verified | `not_hasSDS_of_supportParity` | — |
| [C9](C9.md) | Multiplier theorem with a fixed translate | C2 | proved | — | — |
| [C10](C10.md) | Multiplier-fixed coset sums on a quotient (A7) | C3, C4, C9 | proved | — | — |
| [C11](C11.md) | PDS lemma: λ′ − μ = 2 gives an SDS | — | verified | `IsPDS.hasSDS` | — |
| [C12](C12.md) | NL family: NL_{2^m}(2^(m−1)+1) PDS for every m | C11 | open | — | — |
| [C13](C13.md) | Moments test: C6's arithmetic part, no search | C1, C3, C5 | verified | `not_hasSDS_of_moments` | — |
| [C14](C14.md) | Box bound: C13 with \|a_h\| ≤ c, replaces C6's search | C13 | verified | `not_hasSDS_of_box` | — |
| [C15](C15.md) | C9 for squarefree n: one translate fixed by every multiplier | C1, C2 | verified | `IsSDS.exists_translate_fixed` | — |
| [C16](C16.md) | C10 for squarefree n: multiplier-fixed coset sums | C3, C15 | verified | `IsSDS.exists_translate_fixed_contract` | — |
| [C17](C17.md) | Real characters on a C₂^r quotient: 2^r ∣ s′ + √n·T, T odd | C1, C3 | verified | `not_hasSDS_of_realChars` | — |
| [C18](C18.md) | RDS minus its subgroup: cyclic SDS (n((n+1)²+1), (n+1)²+n, n), n+1 a prime power | — | proved (n ≥ 2) | — | — |
| [C19](C19.md) | Gaussian characters on an exponent-4 quotient: N a₀ = s′ ± m… + 2Σx | C1, C3, C17 | verified | `not_hasSDS_of_gaussChars` | — |
| [C20](C20.md) | Eisenstein characters on an exponent-3 quotient: N a₀ = s′ + Σ(2A − B) | C1, C3, C19 | verified | `not_hasSDS_of_eisensteinChars` | — |
| [C21](C21.md) | Ma's lemma on a mixed quotient C_{p^j} × K: p^⌊e/2⌋ > 2c ⇒ no SDS | C3, C5 | verified | `maRule` | — |
| [C22](C22.md) | Sylow trace rule: p^min(t, ⌈e/2⌉) ∣ s on a p-group quotient (p = 2: equality) | C1, C3 | verified | `not_hasSDS_of_sylow`, `not_hasSDS_of_sylow_two` | — |
| [C23](C23.md) | C5, C13, C14 with a composite modulus (CRT over self-conjugate primes) | C5, C13, C14 | verified | `not_hasSDS_of_compositeModulus` | — |
| [C24](C24.md) | Mod-q vanishing: ψ(D)ψ(D^(−1)) = 0 in characteristic q ∣ n | — | proved | — | — |
| [C25](C25.md) | Self-conjugate primes enlarge the coset-sum multiplier group (N1a) | C5, C10 | open | — | — |
| [C26](C26.md) | Ma descent at equality: an SDS on C_{2^j} × K halves to one on G/P | C1, C3, C21 | proved | — | — |
