# State

**Focus.** Lean for the rules, most rows per effort first: shared infrastructure, then I3 (C5–C7, up to 7,682 rows), then I4 and the 21 objects, then I5. Each rule is one generic theorem plus one kernel check over the rows it settles (find, Settling rows). Paused for the repo migration until the user says to go on.

**Next step.** In order (rows settled in brackets):
- **Phase 0, infrastructure (needed by every rule):**
  1. C1 in Lean (sign sum s, s² = k + λ(v − 1)); a corollary of C3 at the trivial quotient.
  2. `HasSDS` respects group isomorphism, so a rule proved for any finite abelian group reaches each row's nested `ZMod a × ZMod b × …`.
  3. Rows as data (v, k, λ, factors) and the quotient by divisors dᵢ | mᵢ, reusing `Index.lean` and `Contraction.lean`.
- **Phase 1, I3 [up to 7,682]:**
  4. C5 for j = 1 (Frobenius in F_p[H]: y nilpotent and Frobenius-fixed ⇒ y = 0) [3,185].
  5. C5 for j ≥ 2 (the same on (a − tH)/p) [+673].
  6. C6: residue class plus the two moments, a small finite search per row as a kernel check [+3,600].
  7. C7: the marked-count bound, half of it in C4 [+224].
  Each with its row check, chunked (e.g. 500 rows per declaration, one module per build, Resources); the refuter on each Lean statement; `settle.py` once Lean checks.
- **Phase 2, quick wins:**
  8. C8, support parity [553].
  9. C11 and the 21 objects O13–O32 through `answer.py lean` / `fast` [21]; each was already checked against Gordon, He–Chen–Ge and He–Wu by the refuter (found-sets, nl-family).
- **Phase 3, I5 [4,088 + 232]:**
  10. The orbit exhaust (A5) and A7 rerun as experiments on committed code under `solver/`, with the refuter and a second engine; A7's 7,498 unreached rows.
  11. C9 for squarefree n [2,486].
  12. A verified orbit search proved sound once (as `noVector`); C10 on quotients [232+].
- **Phase 4, the rest:**
  13. I6 per row [132]: rerun the all-rows contraction as an experiment; finish E5's 12 first (N93's adaptive split, rebuild the 11 stale contraction Answers one module per call, `#print axioms`, the refuter on them and on C4, `settle.py`).
  14. I8's cheap kill test (the m = 6 recipe at m = 8, 10, Walsh transform) and I7's 49 PDS targets.
  15. C9 for non-squarefree n [1,602]: cyclotomic ideals in Lean, weeks; last or never.
  16. Exhaustion design for the user, only for rows no rule reaches: N70, N75, N76, N77, N134, N135, N136, N138, N140, N177, N178; E7's unreached N133, N204, N205, N207, N212.
- Then one proposed Solution per claim, each answering the table rows it settles (refuter on its Lean statement, then the user).

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
