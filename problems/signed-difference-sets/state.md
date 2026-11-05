# State

**Focus.** Session plan of 2026-11-05 (user), stepped with the user: each step reported, the next only on the user's go, until the user says "go loop".
1. P2: cyclotomic classes of order 8 in GF(q), q ≡ 1 mod 8 (N49's O6 is one, `scratch/refuter/r4-report.md`); every sign (+, −, unmarked) on the classes, 0 marked or not. Which give SDSs, and for which open Instances? A family would be a paper. Minutes of compute.
2. A Lean non-existence checker: first contraction (F3: no integer vector on a quotient meets the conditions; a verified search the kernel evaluates), tested on N32 and the E4 Instances contraction kills; then exhaustion for cases like N3. The design goes to the user before any code: what it proves, how Lean evaluates it, expected speed.
3. Background meanwhile: E4's 9 unchecked sets (N127–N130, N132, N137, N139, N169, N170) as objects, Lean-checked, each checked against Gordon, He–Chen–Ge and He–Wu before it is proposed; E4's 22 unreached Instances with v ≤ 40 finished.
4. Once the checker settles its first cases, the user and the researcher pick the range: open entries with v < 50, v < 100, or more.
**Next step.** Step 2, design approved 2026-11-05. Done: `Index`, `Loops`, `SetCheck` (O12, N35840), `VectorSearch`, `ContractionCheck`, `Tests/Checks` (N32 again, node counts equal E5's). E5's 12 kills as `Answer/N<id>` (`answer.py contract`): 11 of 12 build clean (N79 194 s, N80 83 s, each 7.5 GB peak); N93 (537k nodes, its largest branch 242k) needs the search split across declarations (`goTop`, `noVector_of_top`) to bound kernel memory; then axioms, settle, refuter; then the exhaustion design for the user. Step 1 done.
**Running.**
- E7 (step 3: E4's 22 unreached Instances, 10 threads, below-normal), started 2026-11-05 22:24, output `scratch/e7.out`. 10 done (N131 found a set); **paused** 2026-11-06 00:30 at the user's request (process 33500 suspended with `NtSuspendProcess`; resume with `NtResumeProcess`, it continues where it stopped). Left: N133, N172, N173, N174, N204, N205, N207, N212, and N220, N221, N223, N224 (those four already die by contraction).

**Resources.** One Lean module per `lake build`, through `scratch/lean-build.ps1` (below-normal, killed above 10 GB or under 6 GB free RAM); never several Lean jobs beside an experiment. A parallel build of 12 modules beside E7 froze the user's machine for an hour on 2026-11-05.

## Needs the user
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md`); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Findings to bring to the user: N63319, N14604, N31832, N14471 are settled in Gordon or He–Chen–Ge, so `instances.csv` lists them as open wrongly.
