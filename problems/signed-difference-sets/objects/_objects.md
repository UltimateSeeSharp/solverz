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
| O38 | [O38.txt](O38.txt) | (455, 71, 7) SDS in C₄₅₅, constant on the orbits of a multiplier group of order 12 (41 orbits) | N58470 | E10 | 0 | `Answer.N58470.hasSDS` |
| O39 | [O39.txt](O39.txt) | (300, 55, 6) SDS in C₃₀₀: R − H, R a (50, 6, 49, 8) relative difference set (Bose, projected) relative to the subgroup H of order 6 (C18) | N24177 | refuter (e10-objects, F2) | 0 | — (pending) |
| O40 | [O40.txt](O40.txt) | (125, 28, 3) SDS in C₅ × C₂₅: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N3243 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N3243.hasSDS` |
| O41 | [O41.txt](O41.txt) | (343, 54, 5) SDS in C₇ × C₇ × C₇: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N31721 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N31721.hasSDS` |
| O42 | [O42.txt](O42.txt) | (343, 54, 5) SDS in C₇ × C₄₉: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N31722 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N31722.hasSDS` |
| O43 | [O43.txt](O43.txt) | (125, 97, 72) SDS in C₅ × C₅ × C₅: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N3314 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N3314.hasSDS` |
| O44 | [O44.txt](O44.txt) | (125, 97, 72) SDS in C₅ × C₂₅: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N3315 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N3315.hasSDS` |
| O45 | [O45.txt](O45.txt) | (343, 289, 240) SDS in C₇ × C₇ × C₇: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N32087 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N32087.hasSDS` |
| O46 | [O46.txt](O46.txt) | (343, 289, 240) SDS in C₇ × C₄₉: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N32088 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N32088.hasSDS` |
| O47 | [O47.txt](O47.txt) | (64, 18, 2) SDS in C₂ × C₂ × C₂ × C₂ × C₂ × C₂: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N658 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N658.hasSDS` |
| O48 | [O48.txt](O48.txt) | (64, 18, 2) SDS in C₂ × C₂ × C₂ × C₂ × C₄: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N659 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N659.hasSDS` |
| O49 | [O49.txt](O49.txt) | (64, 18, 2) SDS in C₂ × C₂ × C₂ × C₈: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N660 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N660.hasSDS` |
| O50 | [O50.txt](O50.txt) | (64, 18, 2) SDS in C₂ × C₂ × C₄ × C₄: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N661 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N661.hasSDS` |
| O51 | [O51.txt](O51.txt) | (64, 18, 2) SDS in C₂ × C₄ × C₈: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N663 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N663.hasSDS` |
| O52 | [O52.txt](O52.txt) | (64, 18, 2) SDS in C₄ × C₄ × C₄: R − N, R a semiregular (n², n, n², n) relative difference set, N its forbidden subgroup (I15, F1) | N665 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N665.hasSDS` |
| O53 | [O53.txt](O53.txt) | (64, 46, 30) SDS in C₂ × C₂ × C₂ × C₂ × C₄: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N736 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N736.hasSDS` |
| O54 | [O54.txt](O54.txt) | (64, 46, 30) SDS in C₂ × C₂ × C₂ × C₈: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N737 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N737.hasSDS` |
| O55 | [O55.txt](O55.txt) | (64, 46, 30) SDS in C₂ × C₄ × C₈: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N740 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N740.hasSDS` |
| O56 | [O56.txt](O56.txt) | (64, 46, 30) SDS in C₄ × C₄ × C₄: G − R − N with −1 at 0, R a semiregular (n², n, n², n) relative difference set (I15, F1′) | N742 | ideator round 2 (B4; R by its DFS, `scratch/ideator/r2/f1_64_sets.txt`); `solver/rdscomb.py` | 0 | `Answer.N742.hasSDS` |
| O57 | [O57.txt](O57.txt) | (312, 300, 200) SDS in C₃₁₂: G − 2R − N, R Bose's affine (26, 12, 25, 2) relative difference set projected to C₃₁₂ (I15, F3) | N26075 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N26075.hasSDS` |
| O58 | [O58.txt](O58.txt) | (410, 329, 248) SDS in C₄₁₀: G − R − 2N, R Bose's affine relative difference set projected (I15, F4) | N47314 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N47314.hasSDS` |
| O59 | [O59.txt](O59.txt) | (78, 53, 28) SDS in C₇₈: G − R − 2N, R Bose's affine relative difference set projected (I15, F4) | N1134 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N1134.hasSDS` |
| O60 | [O60.txt](O60.txt) | (200, 151, 102) SDS in C₂₀₀: G − R − 2N, R Bose's affine relative difference set projected (I15, F4) | N9807 | ideator round 2 (B4); `solver/rdscomb.py` | 0 | `Answer.N9807.hasSDS` |
| O61 | [O61.txt](O61.txt) | (42, 18, 2) SDS in C₄₂: generalized cyclotomy on a product of fields (X3) | N236 | ideator round 3 (X3; main folder `scratch/ideator/exists/obj_N236.txt`) | 0 | `Answer.N236.hasSDS` (building) |
| O62 | [O62.txt](O62.txt) | (75, 26, 1) SDS in C₅ × C₁₅: generalized cyclotomy on a product of fields (X3) | N1008 | ideator round 3 (X3; main folder `scratch/ideator/exists/obj_N1008.txt`) | 0 | `Answer.N1008.hasSDS` (building) |
| O63 | [O63.txt](O63.txt) | (217, 112, 12) SDS in C₂₁₇: generalized cyclotomy on a product of fields (X3) | N11602 | ideator round 3 (X3; main folder `scratch/ideator/exists/obj_N11602.txt`) | 0 | `Answer.N11602.hasSDS` (building) |
| O64 | [O64.txt](O64.txt) | (243, 121, 40) SDS in C₃⁵: union of Frobenius orbits of cyclotomic classes of GF(3⁵) (semilinear cyclotomy, X1) | N14597 | ideator round 3 (X1; main folder `scratch/ideator/exists/obj_N14597.txt`) | 0 | `Answer.N14597.hasSDS` (building) |
| O65 | [O65.txt](O65.txt) | (243, 177, 96) SDS in C₃⁵: union of Frobenius orbits of cyclotomic classes of GF(3⁵) (semilinear cyclotomy, X1) | N14828 | ideator round 3 (X1; main folder `scratch/ideator/exists/obj_N14828.txt`) | 0 | `Answer.N14828.hasSDS` (building) |
| O66 | [O66.txt](O66.txt) | (343, 199, 3) SDS in C₇³: union of Frobenius orbits of cyclotomic classes of GF(7³) (semilinear cyclotomy, X1) | N31880 | ideator round 3 (X1; main folder `scratch/ideator/exists/obj_N31880.txt`) | 0 | `Answer.N31880.hasSDS` (building) |
| O67 | [O67.txt](O67.txt) | (343, 247, 51) SDS in C₇³: union of Frobenius orbits of cyclotomic classes of GF(7³) (semilinear cyclotomy, X1) | N31994 | ideator round 3 (X1; main folder `scratch/ideator/exists/obj_N31994.txt`) | 0 | `Answer.N31994.hasSDS` (building) |
| O68 | [O68.txt](O68.txt) | (182, 101, 20) SDS in C₁₈₂: signed combination of a projected Singer relative difference set, d ≥ 3 (X2); the table's stored set is not valid | N7898 | ideator round 3 (X2; main folder `scratch/ideator/exists/obj_N7898.txt`) | 0 | `Answer.N7898.hasSDS` (building) |
| O69 | [O69.txt](O69.txt) | (51, 19, 3) SDS in C₅₁: generalized cyclotomy on a product of fields (X3); the table's stored set is not valid | N388 | ideator round 3 (X3; main folder `scratch/ideator/exists/obj_N388.txt`) | 0 | `Answer.N388.hasSDS` (building) |
| O70 | [O70.txt](O70.txt) | (111, 66, 17) SDS in C₁₁₁: generalized cyclotomy on a product of fields (X3); the table's stored set is not valid | N2554 | ideator round 3 (X3; main folder `scratch/ideator/exists/obj_N2554.txt`) | 0 | `Answer.N2554.hasSDS` (building) |
| O71 | [O71.txt](O71.txt) | (211, 106, 51) SDS in C₂₁₁: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N10864 | I17's mod-q prototype (`scratch/n2/paley.py`) | 0 | `Answer.N10864.hasSDS` (building) |
| O72 | [O72.txt](O72.txt) | (251, 126, 61) SDS in C₂₅₁: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N16190 | I17's mod-q prototype (`scratch/n2/paley.py`) | 0 | `Answer.N16190.hasSDS` (building) |
| O73 | [O73.txt](O73.txt) | (271, 136, 66) SDS in C₂₇₁: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N19488 | I17's mod-q prototype (`scratch/n2/paley.py`) | 0 | `Answer.N19488.hasSDS` (building) |
| O74 | [O74.txt](O74.txt) | (419, 210, 103) SDS in C₄₁₉: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N49190 | I17's mod-q prototype (`scratch/n2/paley.py`) | 0 | `Answer.N49190.hasSDS` (building) |
| O75 | [O75.txt](O75.txt) | (223, 112, 54) SDS in C₂₂₃: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N12056 | built from the residue classes (`scratch/n2`) | 0 | `Answer.N12056.hasSDS` (building) |
| O76 | [O76.txt](O76.txt) | (239, 120, 58) SDS in C₂₃₉: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N13963 | built from the residue classes (`scratch/n2`) | 0 | `Answer.N13963.hasSDS` (building) |
| O77 | [O77.txt](O77.txt) | (263, 132, 64) SDS in C₂₆₃: ±[0] ∓ (quadratic residues or nonresidues), Paley and zero; published (Gordon's database lag, core class 0a), open in the table | N18527 | built from the residue classes (`scratch/n2`) | 0 | `Answer.N18527.hasSDS` (building) |
| O78 | [O78.txt](O78.txt) | (421, 316, 25) SDS in C₄₂₁: −[0] and signs (−1, +1, 0, +1) on the quartic residue classes (index mod 4, g = 2); published (quartic residues, core class 0a), open in the table | N49624 | built from the residue classes (`scratch/n2`) | 0 | `Answer.N49624.hasSDS` (building) |
| O79 | [O79.txt](O79.txt) | (54, 38, 2) SDS in C₃ × C₃ × C₆: P·Z + (1 − u)·T on C₂ × C₃³, Z = O7 (a (27, 10, 1) SDS), T a weight-9 group weighing matrix on C₃³ inside Z's zeros (I21) | N448 | us (`scratch/c26/construct.py`) | 0 | `Answer.N448.hasSDS` (building) |
| O80 | [O80.txt](O80.txt) | (54, 46, 10) SDS in C₃ × C₃ × C₆: P·Z + (1 − u)·T on C₂ × C₃³, Z the Paley-and-zero (27, 14, 5) SDS in GF(27), T a weight-9 weighing matrix inside Z's zeros (I21) | N463 | us (`scratch/c26/construct.py`) | 0 | `Answer.N463.hasSDS` (building) |
| O81 | [O81.txt](O81.txt) | (128, 68, 4) SDS in C₂⁷: P·Z + (1 − u)·T, Z = O47 (a (64, 18, 2) SDS in C₂⁶), T a bent ±1 function on a subgroup of order 16 inside Z's zeros (I21) | N3539 | us (`scratch/c26/construct_coset.py`) | 0 | `Answer.N3539.hasSDS` (building) |
| O82 | [O82.txt](O82.txt) | (72, 40, 4) SDS in C₃ × C₂₄: P·Z + (1 − u)·T on C₈ × C₃², Z = O21 (a (36, 11, 2) SDS), T a weight-9 twisted weighing element (x⁴ = −1 on the C₄ coordinate) inside Z's zeros (I21) | N933 | us (`scratch/c26/construct_twisted.py`) | 0 | `Answer.N933.hasSDS` (building) |
| O83 | [O83.txt](O83.txt) | (72, 40, 4) SDS in C₆ × C₁₂: P·Z + (1 − u)·T on C₂ × C₃ × C₁₂, Z = O21, T a weight-9 group weighing matrix inside Z's zeros (I21) | N934 | us (`scratch/c26/construct.py`) | 0 | `Answer.N934.hasSDS` (building) |
| O84 | [O84.txt](O84.txt) | (72, 40, 4) SDS in C₂ × C₆ × C₆: P·Z + (1 − u)·T, Z = O22 (a (36, 11, 2) SDS in C₆ × C₆), T a weight-9 group weighing matrix inside Z's zeros (I21) | N931 | us (`scratch/c26/construct.py`) | 0 | `Answer.N931.hasSDS` (building) |
