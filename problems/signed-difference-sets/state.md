# State

**Focus.** Lean for the rules, most rows per effort first (find, Settling rows): each rule is one generic theorem plus one kernel check over the rows it settles. Fast track (the user, relayed 2026-11-06): up to 3 Lean helpers plus 2 refuters, all within 7 threads and 13 GB.

**Done in Lean (built, `--wfail`).** Verified: C1 (`Square.lean`), C5 (`SelfConjugacy.lean`), C8 (`Parity.lean`), C13 (`Moments.lean`), C14 (`Box.lean`); infrastructure `Rows.lean`, `Iso.lean`. Row checks: `SelfConjugacyRows/Part01–13` (C5, C13: 6,071 rows), `BoxRows/Part01–03` (C14: 1,387), `ParityRows.lean` (C8: 553, 377 beyond). 7,835 open rows in all, refuters SURVIVE (sc-rows, c1-c8-lean); batch ready in `scratch/settle-rules.tsv`. C14 makes C6's search unnecessary (same 7,458 rows).

**Next step.**
1. Done: 7,835 rows (C5/C13/C14/C8) and 20 objects settled; C7, C17, C15, the I5 orbit search verified (refuter round2).
2. Finish the builds (`scratch/orbit-parts.log` Part01–31, Part19 retry; `scratch/rebuild-names.log`; N58470, N24177), then add every new module to the root (OrbitSearch, OrbitRows/*, MarkedCounts*, GaussChars*, Multiplier is in), root `lake build --wfail` alone, then settle `scratch/settle-round2.tsv` (3,050 rows: C7, C17, I5) and O34–O39's rows; propose the Solutions.
3. C19 (297 rows, Lean built/building): refuter running. C20 (Eisenstein, 144 rows): helper H writing the Lean.
4. Next rules: I5 leaf-heavy squarefree rows (~250, faster leaf); C9 for non-squarefree n (1,992 E10 rows; cyclotomic ideals); characters of order 8/9 quotients; the 74 heavy contraction rows.
5. Later as before: I8's kill test, I7's 49 PDS targets, exhaustion design for the rows no rule reaches.

Results only in scratch (git-ignored):
- The worktree's `scratch/`: `e5.out`, `e6.out`, `e7.out`, `r4.out` (recorded in E5, E6, E7, E4 with SHA-256; `e7.out` still open in the suspended E7); `refuter/n35840-report.md`; `lean-build.ps1` (the RAM watchdog, no committed home: the user's call); `build-*.log`, `bench/*.lean`, `n93_branches.py`, `r5-40.out` (nothing more to record). Keep.
- The **main folder's** `problems/signed-difference-sets/scratch/` (the overnight work of 2026-11-06, outside the worktree; copy it into the worktree's scratch before citing it there): `refuter/` with the reports C5–C12 and the objects cite (`rule-sc`, `extensions`, `a5-a3`, `found-sets`, `db-lags`, `nl-family`, each with its scripts); `ideator/` (report `2026-11-06-0110.md`, rule scripts and outputs); `e8/` (exploration: the all-rows contraction passes, the orbit search, `turyn.py`, README); `other-session/` (another session's hand-off, N735 and N17201). Keep.

**Running.**
- Lean build queues (one module at a time): `scratch/orbit-parts.log`, `scratch/rebuild-names.log`, `scratch/objects-build2.log`.
- Agents (normal limit 3): refuter on C19 (`scratch/refuter/c19/`); helper H, C20 in Lean (`scratch/agentH/`).
- E7, **suspended** 2026-11-06 00:30 at the user's request: process 33500 (`target/release/r4_first_set.exe problems/signed-difference-sets/instances.csv 40 10000000000 10 N70,N71,N76,N77,N131,N133,N168,N172,N173,N174,N176,N177,N178,N194,N204,N205,N207,N212,N220,N221,N223,N224`, from the worktree root, commit 95d6f8c), all threads suspended. Partial output `scratch/e7.out` (11 of 22, E7.md). Resume (PowerShell): `Add-Type -Namespace Win -Name Nt -MemberDefinition '[DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr h);'; [Win.Nt]::NtResumeProcess((Get-Process -Id 33500).Handle)`. If gone, rerun `N133,N204,N205,N207,N212` with the same command, appending to `scratch/e7.out`.

**Resources.** This session is the only one working (the user, 2026-11-06 19:25): all free CPU and RAM, keeping about 2 threads and 4 GB spare (up to 14 threads, ~28 GB), one GPU job at a time, at most 3 agents; below-normal priority, check before compute. Lean: one module per `lake build` through `scratch/lean-build.ps1` (kills above 20 GB or under 4 GB free); kernel-heavy builds alone. A parallel build of 12 modules beside E7 froze the machine on 2026-11-05.

## Needs the user
- Proposed Solutions, settled in `instances.csv` 2026-11-06 (rules, rows of Gordon's table that are Open in sds.json e3bf810 and not ruled out by He–Wu; refuter SURVIVES each Lean statement and its row chunks):
  - C5 (self-conjugacy on a quotient): no SDS in 3,858 rows. Lean: `not_hasSDS_of_selfConj`; rows `SelfConjugacyRows.partNN_not_hasSDS` (rule label C5 in `scratch/sc_certs_all.txt`). Origin: Turyn's self-conjugacy lemma (1965; Lander's form as in Arasu–Gordon–Zhang Thm 2.1) applied to SDS coset sums with the bound 2c < p^j: ours (no published statement for SDS; He–Wu Thm 3.2 has only the odd-exponent case). Refuter: `scratch/refuter/c5-lean`, `sc-rows`.
  - C13 (moments of the coset sums): no SDS in 2,213 more rows. Lean: `not_hasSDS_of_moments`; rows `SelfConjugacyRows.partNN_not_hasSDS` (label C13). Origin: ours (the identities are C3 / He–Wu Lemma 4.1). Refuter: `sc-rows`.
  - C14 (box bound): no SDS in 1,387 more rows. Lean: `not_hasSDS_of_box`; rows `BoxRows.partNN_not_hasSDS`. Origin: ours. Refuter: `sc-rows`.
  - C8 (support parity): no SDS in 553 rows (377 not already covered). Lean: `not_hasSDS_of_supportParity`; rows `ParityRows.parityRows_not_hasSDS`. Origin: for λ = 0 the odd-order weighing-matrix bound (Wallis–Whiteman 1975, Arasu–Seberry 1998); He–Wu Cor 4.5 is its d = 1 case; general λ: ours. Refuter: `c1-c8-lean`.
  - Objects O13–O32 (20 rows Open → exists, settled 2026-11-06): N127–N132, N137, N139 (E4 / r4 search; N130, N132, N137, N139 also by our relative-difference-set construction, found-sets §5), N131 (E7), N169 (E4), N170 (E4; P − {0} for the rook-graph PDS, C11), N286, N638 (E9 orbit search and the ideator), N352 (ideator, order-16 cyclotomic classes of GF(49)), N672, N678, N738, N744, N16957 (refuter nl-family: PDS − {0}, C11), N735, N17201 (other session, NL PDS − {0}). Lean `Answer.N<id>.hasSDS`; refuter SURVIVES (`scratch/refuter/found-sets/report.md`, `nl-family`). Origins as credited there.
  Together 7,835 rows, Open → none: Gordon's table from 68.2% to 79.3% settled (with He–Wu).
- Proposed Solution: N35840, a (361, 316, 141) SDS in C₁₉ × C₁₉ (`Answer.N35840.hasSDS`, O12 from E6). Refuter SURVIVES, claim and status (`scratch/refuter/n35840-report.md` in the worktree); origin ours, citing He–Chen–Ge §5 (cyclotomic SDS framework, classified for order 4 only) and Gordon §3 (order 8 with N = {0}, prime v) as the nearest work.
- Where our status contradicts Gordon's database (sharing it is the user's call; refuter db-lags and a5-a3, main folder's scratch):
  - Open there, settled by a published construction (12): Gordon Prop 2.3: N10864, N12056, N13963, N16190, N18527, N19488, N49190, N14604, N31832; Gordon Thm 4.1: N63319; He–Chen–Ge Prop 5.5(2): N49624; He–Chen–Ge Thm 4.1 with x₁ = 0: N14471 (their Example 4.2, as printed in arXiv v1, is not a signed set). The list is complete for these theorems up to v = 500. The importer credits only N67 and N73 so far.
  - "Yes" there but no construction applies: N63320 (475, 241, 120) in C₄₇₅, filed as "Prime Power Pair", which needs GF(25)'s additive group; it should be open.
  - "Yes" resting only on stored sets that fail the SDS check (147 of 279 stored sets, 21 keys): N388, N1134, N2554, N7891, N7898, N9807 have no valid set on file; N2215 now has one (a5-a3 report).
  - "No" resting on "Orbit Exhaust" with gcd(v, n) > 1, where no multiplier theorem applies: 64 rows, 6 with v ≤ 15 confirmed by exhaustive search, 58 unchecked.
- `scratch/lean-build.ps1` has no committed home.
