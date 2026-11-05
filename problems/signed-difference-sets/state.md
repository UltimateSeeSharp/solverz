# State

**Focus.** R4 (P1 to the first set, every open Instance with v ≤ 40): sets found for N49, N61, N62, N67, N68, N73 (O6–O11), being checked in Lean (`Answer/N<id>`); none for N30, N89, N90 (no Lean proof yet).
**Next step.** Record R4 and the found sets once Lean checks them; then a fast Lean checker for non-existence (contraction with a verified vector search; exhaustion beyond v ≈ 12), so N30, N89, N90 and the contraction kills can be proved.
**Running.**
- R5 (contraction triage, uncommitted `src/contraction.rs`, `src/instances.rs`, `src/bin/r5_contraction.rs`): `target/release/r5_contraction.exe problems/signed-difference-sets/instances.csv 40 10000000 3`, output `scratch/r5-40.out`.
- R4: `target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10` at fc100bc, below-normal priority; output `scratch/r4.out`.

## Needs the user
- Proposed Results, refuter SURVIVES (`scratch/refuter/r4-report.md`), Lean-checked: N49 (25,12,1) in C₅ × C₅; N61 (27,10,1) in C₃³ (origin: He–Chen–Ge's product construction at m = 1, outside their stated m even); N62 (27,10,1) in C₃ × C₉; N68 (27,14,5) in C₃ × C₉. Not Results: N67, N73 are in Gordon 2022 (Prop 2.3, Thm 4.1), Open in the database by mistake.
