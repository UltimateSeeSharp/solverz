# Objects

**Format.** First line: the group's cyclic factors and (v, k, λ). Then one
marked element per line: its coordinates, then `+` or `-`. The Lean form is a
`G → SignType` in `lean/SignedDifferenceSets/Tests/Statement.lean`.

| ID | File | Object | Instance | Source | Score | Lean |
|---|---|---|---|---|---|---|
| O1 | [O1.txt](O1.txt) | (7, 3, 1) difference set {0, 1, 3} in C₇ | — | classical (Singer) | 0 | `Tests.ds731` |
| O2 | [O2.txt](O2.txt) | CW(7, 4) in C₇ | — | classical | 0 | `Tests.cw74` |
| O3 | [O3.txt](O3.txt) | CW(4, 4) in C₄, the circulant Hadamard matrix | — | classical | 0 | `Tests.cw44` |
| O4 | [O4.txt](O4.txt) | (5, 4, −1) SDS in C₅ | N1 | Gordon's table (Yes); triage search | 0 | `Tests.sds541` |
| O5 | [O5.txt](O5.txt) | (9, 8, −1) SDS in C₃ × C₃ | N2 | Gordon's table (Yes); triage search | 0 | `Tests.sds981` |
| O6 | [O6.txt](O6.txt) | (25, 12, 1) SDS in C₅ × C₅ | N49 | E4 | 0 | `Answer.N49.hasSDS` |
| O7 | [O7.txt](O7.txt) | (27, 10, 1) SDS in C₃ × C₃ × C₃ | N61 | E4 | 0 | `Answer.N61.hasSDS` |
| O8 | [O8.txt](O8.txt) | (27, 10, 1) SDS in C₃ × C₉ | N62 | E4 | 0 | `Answer.N62.hasSDS` |
| O9 | [O9.txt](O9.txt) | (27, 14, 5) SDS in C₃ × C₃ × C₃ | N67 | E4 | 0 | `Answer.N67.hasSDS` |
| O10 | [O10.txt](O10.txt) | (27, 14, 5) SDS in C₃ × C₉ | N68 | E4 | 0 | `Answer.N68.hasSDS` |
| O11 | [O11.txt](O11.txt) | (27, 17, 8) SDS in C₃ × C₃ × C₃ | N73 | E4 | 0 | `Answer.N73.hasSDS` |
| O12 | [O12.txt](O12.txt) | (361, 316, 141) SDS in C₁₉ × C₁₉: on GF(361), −(C₀ ∪ … ∪ C₅ ∪ {0}) + C₇ over the octic classes, up to an automorphism and sign | N35840 | E6 | 0 | `Answer.N35840.hasSDS` |
| O13 | [O13.txt](O13.txt) | (32, 20, 4) SDS in C₂ × C₁₆ | N131 | E7 | 0 | — (pending) |
| O14 | [O14.txt](O14.txt) | (32, 20, 4) SDS in C₂⁵ | N127 | E4 (worktree `scratch/r4.out`); refuter SURVIVES (`scratch/refuter/found-sets/report.md`) | 0 | — |
| O15 | [O15.txt](O15.txt) | (32, 20, 4) SDS in C₂³ × C₄ | N128 | E4; refuter SURVIVES (found-sets) | 0 | — |
| O16 | [O16.txt](O16.txt) | (32, 20, 4) SDS in C₂² × C₈ | N129 | E4; refuter SURVIVES (found-sets) | 0 | — |
| O17 | [O17.txt](O17.txt) | (32, 20, 4) SDS in C₂ × C₄ × C₄ | N130 | E4; refuter SURVIVES (found-sets; also from a (4,4,4,1) relative difference set in C₄ × C₄) | 0 | — |
| O18 | [O18.txt](O18.txt) | (32, 20, 4) SDS in C₄ × C₈ | N132 | E4; refuter SURVIVES (found-sets; same relative-difference-set construction) | 0 | — |
| O19 | [O19.txt](O19.txt) | (32, 28, 12) SDS in C₂ × C₄ × C₄ | N137 | E4; refuter SURVIVES (found-sets; relative difference set in C₄ × C₄) | 0 | — |
| O20 | [O20.txt](O20.txt) | (32, 28, 12) SDS in C₄ × C₈ | N139 | E4; refuter SURVIVES (found-sets; same construction) | 0 | — |
| O21 | [O21.txt](O21.txt) | (36, 11, 2) SDS in C₃ × C₁₂ | N169 | E4; refuter SURVIVES (found-sets) | 0 | — |
| O22 | [O22.txt](O22.txt) | (36, 11, 2) SDS in C₆ × C₆ | N170 | E4; refuter SURVIVES (found-sets: P − {0} for the rook-graph PDS, C11) | 0 | — |
| O23 | [O23.txt](O23.txt) | (45, 37, 1) SDS in C₃ × C₁₅, constant on the orbits of x ↦ 2x | N286 | exploration (`scratch/e8/e9-200.out`) and ideator, the same set; refuter SURVIVES (found-sets) | 0 | — |
| O24 | [O24.txt](O24.txt) | (49, 33, 1) SDS in C₇ × C₇, union of order-16 cyclotomic classes of GF(49) | N352 | ideator (`scratch/ideator/`); refuter SURVIVES (found-sets) | 0 | — |
| O25 | [O25.txt](O25.txt) | (63, 47, 11) SDS in C₃ × C₂₁, constant on the orbits of x ↦ 2x | N638 | exploration (`scratch/e8/e9-200.out`) and ideator, the same set; refuter SURVIVES (found-sets) | 0 | — |
| O26 | [O26.txt](O26.txt) | (64, 22, 6) SDS in C₂² × C₄²: P − {0}, P the 3-subgroup partial congruence partition (C11) | N672 | refuter (`scratch/refuter/nl-family/`, F11), checked on every shift | 0 | — |
| O27 | [O27.txt](O27.txt) | (64, 22, 6) SDS in C₈ × C₈: P − {0}, the same partial congruence partition (C11) | N678 | refuter (nl-family, F11) | 0 | — |
| O28 | [O28.txt](O28.txt) | (64, 46, 30) SDS in C₂⁶: P − {0}, P the complement of the hyperoval PDS T₂*(O), NL₈(5) (C11, C12) | N735 | other session (`scratch/other-session/`); refuter SURVIVES (nl-family) | 0 | — |
| O29 | [O29.txt](O29.txt) | (64, 46, 30) SDS in C₂² × C₄²: P − {0}, P an NL₈(5) PDS (C11, C12) | N738 | refuter (nl-family, F9) | 0 | — |
| O30 | [O30.txt](O30.txt) | (64, 46, 30) SDS in C₈ × C₈: P − {0}, P an NL₈(5) PDS (C11, C12) | N744 | refuter (nl-family) | 0 | — |
| O31 | [O31.txt](O31.txt) | (256, 106, 42) SDS in C₁₆ × C₁₆: P − {0}, P an L₁₆(7) PDS (C11) | N16957 | refuter (nl-family) | 0 | — |
| O32 | [O32.txt](O32.txt) | (256, 154, 90) SDS in C₂⁸: P − {0}, P three of the five order-5 classes of GF(256), NL₁₆(9) (C11, C12) | N17201 | other session; refuter SURVIVES (nl-family) | 0 | — |
| O33 | [O33.txt](O33.txt) | (4096, 2146, 1122) SDS in C₂¹²: P − {0}, P an NL₆₄(33) PDS from 30 norm classes of GF(2¹²) (C11, C12); beyond the table | — | refuter (nl-family, `verify_m6.py`), checked on every shift | 0 | — |
| O34 | [O34.txt](O34.txt) | (79, 61, 38) SDS in C₇₉, constant on the orbits of a multiplier group of order 3 (27 orbits) | N1164 | E10 | 0 | — (pending) |
| O35 | [O35.txt](O35.txt) | (127, 109, 90) SDS in C₁₂₇, constant on the orbits of a multiplier group of order 3 (43 orbits) | N3486 | E10 | 0 | — (pending) |
| O36 | [O36.txt](O36.txt) | (217, 193, 168) SDS in C₂₁₇, constant on the orbits of a multiplier group of order 6 (42 orbits) | N11650 | E10 | 0 | — (pending) |
| O37 | [O37.txt](O37.txt) | (222, 69, 20) SDS in C₂₂₂, constant on the orbits of a multiplier group of order 9 (30 orbits) | N11991 | E10 | 0 | — (pending) |
| O38 | [O38.txt](O38.txt) | (455, 71, 7) SDS in C₄₅₅, constant on the orbits of a multiplier group of order 12 (41 orbits) | N58470 | E10 | 0 | — (pending) |
| O39 | [O39.txt](O39.txt) | (300, 55, 6) SDS in C₃₀₀: R − H, R a (50, 6, 49, 8) relative difference set (Bose, projected) relative to the subgroup H of order 6 (C18) | N24177 | refuter (e10-objects, F2) | 0 | — (pending) |
