# State

**Focus.** Paused for a repo migration by the user (2026-11-06): nothing new starts until the user says so. The session plan of 2026-11-05 (user), stepped with the user (each step reported, the next only on the user's go, until the user says "go loop"):
1. P2, octic cyclotomic sets: done (E6, sporadic; N35840 found, O12).
2. A Lean non-existence checker: contraction done and checked by the kernel (`VectorSearch`, `ContractionCheck`; 11 of E5's 12 kills build); exhaustion still to design, shown to the user before any code.
3. Background: E4's 9 found but unchecked sets as objects, Lean-checked and compared with the known constructions; E4's 22 unreached Instances (E7, suspended at 11).
4. With the user, once the checker settles its first cases: the range (open entries with v < 50, v < 100, or more).

**Next step.** In order:
1. Contraction, N93: make `answer.py contract`'s split adaptive (split only branches above `BRANCH_NODES`; uniform depth gives N93 1,114 checks at depth 6), then `python -I solver/answer.py contract N93 2,7` and build it alone with `scratch/lean-build.ps1`; add it to `SignedDifferenceSets.lean`.
2. Rebuild: `VectorSearch.lean` changed after the 11 contraction Answers were built, so `ContractionCheck`, `Tests.Checks` and Answer N46, N47, N79, N80, N95, N168, N176, N220, N221, N223, N224 are stale. Rebuild one module per call through `scratch/lean-build.ps1`; never `lake build` the root while they are stale (Lake would build them in parallel).
3. `#print axioms` of the 12 `Answer.N<id>.not_hasSDS` (one scratch file importing them, one Lean process); then the refuter on them, on F4, on `noVector_sound` / `not_hasSDS_of_noVector`, and on each Instance's literature status; then `settle.py N<id> none "E5; F3; F4" SignedDifferenceSets.Answer.N<id>.not_hasSDS`, journal lines, and each proposed under "Needs the user".
4. Exhaustion design for the user (step 2): Instances P1 exhausted that contraction does not kill: N30, N75, N89, N90, N99, N134, N135, N136, N138, N140 (E4); N70, N71, N76, N77, N177, N178, N194 (E7). Kernel exhaustion runs about 300 P1 nodes/s, these need 10⁸ to 10¹⁰; options: lift above the contraction vectors, more symmetry, SAT with LRAT proofs checked by Mathlib's `lrat_proof` (a SAT solver install is the user's call).
5. Step 3: O13 (N131, E7) to Lean (`answer.py fast O13 N131`), compared with Gordon, He–Chen–Ge, He–Wu, then the refuter. E4's 9 sets (N127–N130, N132, N137, N139, N169, N170): `answer.py object scratch/r4.out N<id> O<n>` (O14 on), Lean, constructions, refuter. Resume E7 (Running).

Results only in scratch (git-ignored):
- `scratch/e5.out`, `scratch/e6.out`, `scratch/e7.out`, `scratch/r4.out`: run outputs, recorded in E5, E6, E7, E4 with SHA-256 (`e7.out` is still open in the suspended E7). Keep.
- `scratch/refuter/n35840-report.md` (and its scripts, logs): the refuter's SURVIVES on N35840, cited under "Needs the user". Keep.
- `scratch/lean-build.ps1`: the RAM watchdog every Lean build goes through (Resources). Tooling, not committed: it needs a committed home or must be kept (the user's call).
- `scratch/build-*.log`: Lean build logs (N79 194 s, N80 83 s, 7.5 GB peak each); nothing more to record.
- `scratch/bench/*.lean`: kernel speed probes (10⁴ loop steps 0.4 s, 10⁵ 5 s, 10⁶ 110 s; v = 361 set-check loop 65 s); recorded in understanding.md.
- `scratch/n93_branches.py`, `scratch/r5-40.out`: exploration, superseded by `answer.py` (`prefix_nodes`) and E5; nothing to record.

**Running.**
- E7, **suspended** 2026-11-06 00:30 at the user's request: process 33500 (`target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10 N70,N71,N76,N77,N131,N133,N168,N172,N173,N174,N176,N177,N178,N194,N204,N205,N207,N212,N220,N221,N223,N224`, from the worktree root, commit 95d6f8c), all threads suspended, below-normal, ~1 MB RAM. Partial output `scratch/e7.out` (11 of 22, E7.md). Resume (PowerShell): `Add-Type -Namespace Win -Name Nt -MemberDefinition '[DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr h);'; [Win.Nt]::NtResumeProcess((Get-Process -Id 33500).Handle)`; it continues mid-search. If the process is gone (reboot), rerun the unfinished IDs with the same command, ID list `N172,N173,N174,N204,N205,N207,N212` (N220, N221, N223, N224 die by contraction), appending to `scratch/e7.out`; the search is deterministic.
- No agents (the refuter on N35840 finished).

**Resources.** One Lean module per `lake build`, through `scratch/lean-build.ps1` (below-normal, killed above 10 GB or under 6 GB free RAM); never several Lean jobs beside an experiment. A parallel build of 12 modules beside E7 froze the user's machine for an hour on 2026-11-05.

## Needs the user
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md`); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Findings to bring to the user: N63319, N14604, N31832, N14471 are settled in Gordon or He–Chen–Ge, so `instances.csv` lists them as open wrongly.
- `scratch/lean-build.ps1` has no committed home (see above).
