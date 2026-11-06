# State

**Focus.** Lean for the rules, most rows per effort first (find, Settling rows): each rule is one generic theorem plus one kernel check over the rows it settles. Fast track (the user, relayed 2026-11-06): up to 3 Lean helpers plus 2 refuters, all within 7 threads and 13 GB.

**Done in Lean (built, `--wfail`).** Phase 0: `Rows.lean` (row groups as data), `Square.lean` (C1), `Iso.lean`, `Parity.lean` (C8). C5 verified (`SelfConjugacy.lean`, any j). C13 = C6's arithmetic part (`Moments.lean`). Row checker `SelfConjugacyCheck.lean`; generators `solver/selfconj.py` (C5/C13 certificates, 6,071 rows: 3,858 C5 + 2,213 C13) and `solver/parity.py` (C8, 553 rows, 434 beyond). Pds.lean (C11) and the 20 object Answers by helper B, not yet integrated.

**Next step.**
1. Build `SelfConjugacyRows/Part01`–`Part13` (running, one at a time; Part01 33 s) and `ParityRows.lean`; import all new modules in the library root; root build alone (Contraction was rebuilt, so the stale answers downstream rebuild too).
2. On the refuters' verdicts: C13 and the row chunks (sc-rows), C1, C8, Rows, Iso (c1-c8-lean). Then settle the rows (`settle.py`, batch), journal, and one proposed Solution per rule under "Needs the user".
3. Integrate helper B (C11, objects O13–O32: `lake build` each alone, refuter on C11's statement), helper C (E10 orbit exhaust: review, commit, launch), helper D (C9 squarefree in Lean).
4. C7 (marked counts) and C6's search part (R2dp, ~1,387 rows): a verified DP; then I5 per row (orbit exhaust in Lean) once C9 lands.
5. Later as before: E5's N93 split and stale rebuilds, I8's kill test, I7's 49 PDS targets, C9 for non-squarefree n, exhaustion design for the rows no rule reaches.

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in the suspended E7); `refuter/n35840-report.md`; `lean-build.ps1` (the RAM watchdog, no committed home: the user's call); `build-*.log`, `bench/*.lean`, `n93_branches.py`, `r5-40.out` (nothing more to record). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): `refuter/` with the reports C5–C12 and the objects cite (`rule-sc`, `extensions`, `a5-a3`, `found-sets`, `db-lags`, `nl-family`, each with its scripts); `ideator/` (report `2026-11-06-0110.md`, rule scripts and outputs); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

**Running.**
- Lean builds of `SelfConjugacyRows/Part02`–`13` (started 2026-11-06 ~16:20, log `scratch/sc-parts.log`).
- Helper B (agent, Lean): C11 `Pds.lean` done; checking Answer files O13–O32 alone (`scratch/agentB/progress.md`).
- Helper C (agent, Rust, ≤ 3 threads): I5 orbit exhaust engine `solver/src/orbits.rs`, `e10_orbit_exhaust.rs`, validation, draft E10 (`scratch/agentC/`); no full run before review.
- Helper D (agent, Lean): C9 for squarefree n, `Multiplier.lean` (`scratch/agentD/progress.md`).
- Refuter sc-rows: C13, the checker and the 13 chunks (`scratch/refuter/sc-rows/`). Refuter c1-c8-lean: C1, C8, Rows, Iso (`scratch/refuter/c1-c8-lean/`).
- E7, **suspended** 2026-11-06 00:30 at the user's request: process 33500 (`target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10 N70,N71,N76,N77,N131,N133,N168,N172,N173,N174,N176,N177,N178,N194,N204,N205,N207,N212,N220,N221,N223,N224`, from the worktree root, commit 95d6f8c), all threads suspended. Partial output `scratch/e7.out` (11 of 22, E7.md). Resume (PowerShell): `Add-Type -Namespace Win -Name Nt -MemberDefinition '[DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr h);'; [Win.Nt]::NtResumeProcess((Get-Process -Id 33500).Handle)`. If gone, rerun `N133,N204,N205,N207,N212` with the same command, appending to `scratch/e7.out`.

**Resources.** This session with all its agents: at most 7 threads and 13 GB RAM (another session shares the PC; the user works on it), below-normal priority, at most 2 light Lean processes at once, heavy kernel checks alone. One Lean module per `lake build`, through `scratch/lean-build.ps1` (below-normal, killed above 10 GB or under 6 GB free RAM); never several Lean jobs beside an experiment. A parallel build of 12 modules beside E7 froze the user's machine for an hour on 2026-11-05. Agents and experiments together keep 2 threads spare: a 10-process agent job beside a 12-thread search froze the machine on 2026-11-06.

## Needs the user
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md` in the worktree); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Where our status contradicts Gordon's database (sharing it is the user's call; refuter db-lags and a5-a3, main folder's scratch):
  - Open there, settled by a published construction (12): Gordon Prop 2.3: N10864, N12056, N13963, N16190, N18527, N19488, N49190, N14604, N31832; Gordon Thm 4.1: N63319; He–Chen–Ge Prop 5.5(2): N49624; He–Chen–Ge Thm 4.1 with x₁ = 0: N14471 (their Example 4.2, as printed in arXiv v1, is not a signed set). The list is complete for these theorems up to v = 500. The importer credits only N67 and N73 so far.
  - "Yes" there but no construction applies: N63320 (475, 241, 120) in C₄₇₅, filed as "Prime Power Pair", which needs GF(25)'s additive group; it should be open.
  - "Yes" resting only on stored sets that fail the SDS check (147 of 279 stored sets, 21 keys): N388, N1134, N2554, N7891, N7898, N9807 have no valid set on file; N2215 now has one (a5-a3 report).
  - "No" resting on "Orbit Exhaust" with gcd(v, n) > 1, where no multiplier theorem applies: 64 rows, 6 with v ≤ 15 confirmed by exhaustive search, 58 unchecked.
- `scratch/lean-build.ps1` has no committed home.
