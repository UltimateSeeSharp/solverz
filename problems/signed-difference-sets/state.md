# State

**Focus.** Lean for the rules, most rows per effort first (find, Settling rows): each rule is one generic theorem plus one kernel check over the rows it settles. Fast track (the user, relayed 2026-11-06): up to 3 Lean helpers plus 2 refuters, all within 7 threads and 13 GB.

**Done in Lean (built, `--wfail`).** Verified: C1 (`Square.lean`), C5 (`SelfConjugacy.lean`), C8 (`Parity.lean`), C13 (`Moments.lean`), C14 (`Box.lean`); infrastructure `Rows.lean`, `Iso.lean`. Row checks: `SelfConjugacyRows/Part01–13` (C5, C13: 6,071 rows), `BoxRows/Part01–03` (C14: 1,387), `ParityRows.lean` (C8: 553, 377 beyond). 7,835 open rows in all, refuters SURVIVE (sc-rows, c1-c8-lean); batch ready in `scratch/settle-rules.tsv`. C14 makes C6's search unnecessary (same 7,458 rows).

**Next step.**
1. Root build (running: the 17 stale modules one at a time, heavy ones alone, then `SignedDifferenceSets`; log `scratch/stale-rebuild.log`). On success: `python -I solver/import/settle.py --batch scratch/settle-rules.tsv`, journal, one proposed Solution per rule (C5, C13, C14, C8) under "Needs the user".
2. Integrate helper B (C11 `Pds.lean`, Answers O13–O32 checked clean by `lake env lean`: `lake build` each, refuter on C11's statement, `settle.py` for the objects' rows).
3. I5 in Lean: helper D (C9 for squarefree n) + helper E (verified orbit search); E10 supplies the rows and their multipliers. Then the A5 rows with squarefree n per row.
4. C7 (224 rows): LP dual certificates if the relaxation kills them (`scratch/c7_lp.py`, running).
5. Later as before: E5's N93 split, the contraction rows E8 killed (91 open), I8's kill test, I7's 49 PDS targets, C9 for non-squarefree n, exhaustion design for the rows no rule reaches.

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in the suspended E7); `refuter/n35840-report.md`; `lean-build.ps1` (the RAM watchdog, no committed home: the user's call); `build-*.log`, `bench/*.lean`, `n93_branches.py`, `r5-40.out` (nothing more to record). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): `refuter/` with the reports C5–C12 and the objects cite (`rule-sc`, `extensions`, `a5-a3`, `found-sets`, `db-lags`, `nl-family`, each with its scripts); `ideator/` (report `2026-11-06-0110.md`, rule scripts and outputs); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

**Running.**
- Lean build queues, one module at a time: `scratch/stale-rebuild.log` (stale contraction answers, then root; N32 regenerated with `noVector`, N80 killed at 9 GB, retried alone at 13 GB), then `scratch/objects-build.log` (C11 `Pds`, N32, the 20 answers O13–O32), then `scratch/objects-build2.log` (O34–O38's answers, N80).
- E10 orbit exhaust (pid 35192, 3 threads, below normal), started 2026-11-06 16:39, output `scratch/e10.out`; at 17:05 8,049 of 12,209 rows (7,546 none, 14 found, 489 cut); the rest (> 40 orbits) mostly cut at ~10 s each, ~3–4 h. Resumable (E10.md).
- `scratch/c7_lp.py` (C7's LP relaxation on its 224 rows), output `scratch/c7_lp.out`.
- Helper E (Lean): verified orbit search, `OrbitSearch.lean` (`scratch/agentE/`), then the I5 row theorem with C15.
- Refuter e10-objects: O34–O38 (E10's sets for N1164, N3486, N11650, N11991, N58470: new or known?) and C11's Lean statement (`scratch/refuter/e10-objects/`).
- E7, **suspended** 2026-11-06 00:30 at the user's request: process 33500 (`target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10 N70,N71,N76,N77,N131,N133,N168,N172,N173,N174,N176,N177,N178,N194,N204,N205,N207,N212,N220,N221,N223,N224`, from the worktree root, commit 95d6f8c), all threads suspended. Partial output `scratch/e7.out` (11 of 22, E7.md). Resume (PowerShell): `Add-Type -Namespace Win -Name Nt -MemberDefinition '[DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr h);'; [Win.Nt]::NtResumeProcess((Get-Process -Id 33500).Handle)`. If gone, rerun `N133,N204,N205,N207,N212` with the same command, appending to `scratch/e7.out`.

**Resources.** This session with all its agents: at most 7 threads and 20 GB RAM (from 16:38) (another session shares the PC; the user works on it), below-normal priority, at most 3 light Lean processes at once, heavy kernel checks alone. One Lean module per `lake build`, through `scratch/lean-build.ps1` (below-normal, killed above 10 GB or under 6 GB free RAM); never several Lean jobs beside an experiment. A parallel build of 12 modules beside E7 froze the user's machine for an hour on 2026-11-05. Agents and experiments together keep 2 threads spare: a 10-process agent job beside a 12-thread search froze the machine on 2026-11-06.

## Needs the user
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md` in the worktree); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Where our status contradicts Gordon's database (sharing it is the user's call; refuter db-lags and a5-a3, main folder's scratch):
  - Open there, settled by a published construction (12): Gordon Prop 2.3: N10864, N12056, N13963, N16190, N18527, N19488, N49190, N14604, N31832; Gordon Thm 4.1: N63319; He–Chen–Ge Prop 5.5(2): N49624; He–Chen–Ge Thm 4.1 with x₁ = 0: N14471 (their Example 4.2, as printed in arXiv v1, is not a signed set). The list is complete for these theorems up to v = 500. The importer credits only N67 and N73 so far.
  - "Yes" there but no construction applies: N63320 (475, 241, 120) in C₄₇₅, filed as "Prime Power Pair", which needs GF(25)'s additive group; it should be open.
  - "Yes" resting only on stored sets that fail the SDS check (147 of 279 stored sets, 21 keys): N388, N1134, N2554, N7891, N7898, N9807 have no valid set on file; N2215 now has one (a5-a3 report).
  - "No" resting on "Orbit Exhaust" with gcd(v, n) > 1, where no multiplier theorem applies: 64 rows, 6 with v ≤ 15 confirmed by exhaustive search, 58 unchecked.
- `scratch/lean-build.ps1` has no committed home.
