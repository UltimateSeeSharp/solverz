# State

**Focus.** Settle the most rows first: the rules I3 (7,682 rows), I5 (4,088 + 232), I4 (553) need their Lean theorems; the 21 refuter-checked sets (O13–O32) need Lean; then I6's per-row searches and the constructions I7, I8. Paused for the repo migration until the user says to go on.

**Next step.** In order (rows settled per step in brackets):
1. I3 in Lean [up to 7,682]: C5 for j = 1 first (Frobenius in F_p[H], y nilpotent and Frobenius-fixed ⇒ y = 0; 3,185 of C5's 3,858 rows), in its topic file with one Lean check over all its rows (find, Settling rows); then j ≥ 2, C6, C7. The refuter on each Lean statement; `settle.py` once Lean checks.
2. I5 [4,088 + 232]: the orbit exhaust (A5) and A7 as experiments on committed code under `solver/` (the ideator's Python is exploration), the refuter and a second engine on them, A7's 7,498 unreached rows; Lean: C9 for squarefree n (2,486 rows) first.
3. I4 in Lean [553]: C8, the easiest rule.
4. Objects to Lean [21]: O13–O32 through `answer.py lean` / `fast` (one module at a time, Resources); each was checked against Gordon, He–Chen–Ge and He–Wu by the refuter (found-sets, nl-family), so each goes under "Needs the user" as a proposed Solution once Lean checks it.
5. I6 [132]: rerun the all-rows contraction (exploration in the main folder's `scratch/e8/`) as an experiment; finish E5's 12 first: N93's adaptive split (`answer.py contract N93 2,7`), rebuild the 11 stale contraction Answers one module per call, `#print axioms`, the refuter on them and on C4, then `settle.py`.
6. I8's cheap kill test (the m = 6 norm-class recipe at m = 8, 10 with a Walsh transform, minutes); I7's 49 PDS targets (`lemma_targets.out`).
7. Exhaustion design for the user, now only for rows no rule reaches: N70, N75, N76, N77, N134, N135, N136, N138, N140, N177, N178 (C5/C6, C8 and A5 cover N30, N71, N89, N90, N99, N194); E7's unreached N133, N204, N205, N207, N212 (N172–N174 die by C6).

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in the suspended E7); `refuter/n35840-report.md`; `lean-build.ps1` (the RAM watchdog, no committed home: the user's call); `build-*.log`, `bench/*.lean`, `n93_branches.py`, `r5-40.out` (nothing more to record). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): `refuter/` with the reports C5–C12 and the objects cite (`rule-sc`, `extensions`, `a5-a3`, `found-sets`, `db-lags`, `nl-family`, each with its scripts); `ideator/` (report `2026-11-06-0110.md`, rule scripts and outputs); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

**Running.**
- E7, **suspended** 2026-11-06 00:30 at the user's request: process 33500 (`target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10 N70,N71,N76,N77,N131,N133,N168,N172,N173,N174,N176,N177,N178,N194,N204,N205,N207,N212,N220,N221,N223,N224`, from the worktree root, commit 95d6f8c), all threads suspended, below-normal, ~1 MB RAM. Partial output `scratch/e7.out` (11 of 22, E7.md). Resume (PowerShell): `Add-Type -Namespace Win -Name Nt -MemberDefinition '[DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr h);'; [Win.Nt]::NtResumeProcess((Get-Process -Id 33500).Handle)`; it continues mid-search. If the process is gone (reboot), rerun the unfinished IDs `N133,N204,N205,N207,N212` with the same command, appending to `scratch/e7.out`; the search is deterministic (N172–N174 die by C6, N220, N221, N223, N224 by contraction).
- No agents.

**Resources.** One Lean module per `lake build`, through `scratch/lean-build.ps1` (below-normal, killed above 10 GB or under 6 GB free RAM); never several Lean jobs beside an experiment. A parallel build of 12 modules beside E7 froze the user's machine for an hour on 2026-11-05. Agents and experiments together keep 2 threads spare: a 10-process agent job beside a 12-thread search froze the machine on 2026-11-06.

## Needs the user
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md` in the worktree); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Where our status contradicts Gordon's database (sharing it is the user's call; refuter db-lags and a5-a3, main folder's scratch):
  - Open there, settled by a published construction (12): Gordon Prop 2.3: N10864, N12056, N13963, N16190, N18527, N19488, N49190, N14604, N31832; Gordon Thm 4.1: N63319; He–Chen–Ge Prop 5.5(2): N49624; He–Chen–Ge Thm 4.1 with x₁ = 0: N14471 (their Example 4.2, as printed in arXiv v1, is not a signed set). The list is complete for these theorems up to v = 500. The importer credits only N67 and N73 so far.
  - "Yes" there but no construction applies: N63320 (475, 241, 120) in C₄₇₅, filed as "Prime Power Pair", which needs GF(25)'s additive group; it should be open.
  - "Yes" resting only on stored sets that fail the SDS check (147 of 279 stored sets, 21 keys): N388, N1134, N2554, N7891, N7898, N9807 have no valid set on file; N2215 now has one (a5-a3 report).
  - "No" resting on "Orbit Exhaust" with gcd(v, n) > 1, where no multiplier theorem applies: 64 rows, 6 with v ≤ 15 confirmed by exhaustive search, 58 unchecked.
- `scratch/lean-build.ps1` has no committed home.
