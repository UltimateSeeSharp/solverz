# Refuter C27/C28 notes (2026-11-07)

Started ~02:50. Brief: scratch/refuter-not-kept/c27-brief.md.

## Read so far
- C27.md, C28.md, I10.md, Statement.lean, UnramifiedDescent.lean, Tests/UnramifiedDescent.lean, C10 statement (MultiplierWitt.lean:549).
- Kills (UnramifiedDescent.lean:243-251): n>0, gcd(m,n)=1, F|m, every t=1+Fu (u<m/F) coprime to m and = p^e mod m
  (e<m) for each prime p|n (prime = no divisor in [2,p)), kill m F (v/m)^2 < phi(m) n.
- not_hasSDS concludes ¬HasSDS (Grp w.ms) w.k w.lam for any Fintype inst. OK.
- check_rows.py (independent): 259 rows parsed, 259 distinct ids, all match instances.csv key (k, lam, ms, v=prod) and are `open`;
  Kills re-evaluated literally (Lean semantics incl. MapOk/SurjCert/prime test) and mathematically (intersection of <p> mod m): 0 issues.
- scan_exists.py (independent, broader: every divisor F of m, every m | exp G coprime to n): exists 0/214 fire;
  open: exactly the 259 Lean ids (hits_open.txt vs Lean ids: same set).
- objects_check.py: 104 objects, 444 (quotient, form) pairs with gcd(m,n)=1: C10 translate fixed by whole multiplier group
  in all 444; chi_a(Y)=chi_a(Y_S) and |chi|^2=n numerically for every unit a and admissible F (454 tests, ~10 with F<m); bound never violated.
- C27 math re-derived by hand: substitution h -> t h (t unit), average over u<d, geometric sum of d-th roots w=zeta^(aFh); a unit so
  aFh=0 iff Fh=0; Parseval over all a; |S|=F exactly. C10 sign: s=0 would force m | n (s^2 = n + lam v), so +1 sign is forced; ok.
  Lean IsSDS.totient_mul_le feeds C10's t-condition (t = p^e mod m, i.e. on ZMod m, exp = m) exactly. Kills: F=0 impossible (F|m, m>1).
## C28
- Read EvenContraction.lean fully. EvenCert.Ok: r,i>0, ks≠[], d | 2^i+1 (so 2^i = -1 on K), MapOk/SurjCert to ZMod(2r) x Grp ks,
  2r|K| divides v, 4|n, s^2 = k+lam(v-1), s even, 4 | k+lam(2c-1), 2 | lam c, K≡s/2 mod 2, k<2K+4, (2,r) in maPairs. Matches claim.
- 8 rows: N664,N675,N741,N763 ([2,32], r=16, K=1), N4672,N4712,N4762 ([2,72], r=1, K=Z9, i=3), N20961 ([280], r=2, K=Z5, i=2).
  Hand-checked s, Q, t, K for all 8. N675/N741/N763 reduce by hand to a cyclic (16,6,2) difference set (none exists): consistent.
- All 8 C28 rows `open`, keys match (instances.csv).
- even_objects.py: 50 objects with 4|n, 275 quotient forms Z_(2r) x Z_d (r power of 2, d | 2^i+1): Ma step, W even, every Z demand holds. 0 fails.
- even_rows_search.py (independent, exact Fractions, variance pruning): all 8 rows 0 vectors (both signs of s2).
  Positive controls running (even_controls.py; first run only trivial L found 2 sols each).
- Literature: Tan arXiv:1610.01914 opened (PDF text via PyMuPDF): Def 2.10 F(v,n), Result 2.11 (Schmidt descent, X zeta^j in Z[zeta_F]),
  Result 2.12 F-bound n <= C^2 F^2/phi(F); Result 3.2 McFarland multiplier thm (gcd(v,n)=1, t = p_i^f_i mod exp) + fixed translate (= C10).
- C27 rows vs scratch/c26/fbound_kills.txt (Schmidt F-bound with Tan's F): 258/259 also killed by Schmidt; N9792 SDS(200,139,18,[2,100])
  is NOT: m=100, n=121, <11> mod 100 = 1+10Z so C27's F=10, but Tan's F(100,121)=gcd(100, 2^3 5)=20 (n<=200, no kill).
  C27 is sharper here because C10's translate absorbs the root-of-unity cocycle (Y^(11)=Y g with 10|g by McFarland-Rice) that
  forces Schmidt's 2-adic exponent b(2)>=2. Hand check: on Z_10 descent, 4 units*121=484 > 10*(10*4)=400. Kill valid given C10.
  => claim text "This is Schmidt's bound for n prime to m" is slightly inaccurate (C27 can beat F(m,n)); not a flaw.
- rad(m) | F is forced by the Lean coprimality condition (p|m, p∤F => some 1+Fu ≡ 0 mod p with u<p<=d), so m/phi(m)=F/phi(F) and
  C27's bound is n <= c^2 F^2/phi(F): Schmidt's form with the multiplier F.
- He–Wu arXiv:2608.22936 v2 (opened, text extracted): no field descent / Schmidt / F-bound / Ma; their 4 obstructions are already
  applied by solver/import (README), and all 259+8 rows are still open after them. Gordon arXiv:2212.10630 (opened): uses McFarland
  multiplier thm (Thm 5.1), no field descent. Tan 1610.01914 Sec 4.1 applies the F-bound to group-invariant weighing matrices (lam=0);
  no C27 row has lam=0 (all lam>=1). Web search "signed difference sets ... field descent multiplier bound": nothing on SDS field descent.
- 03:08 Report drafted: reviews/R29/report-2026-11-07-0305.md (C27 1-4, C28 1-3, literature). Pending:
  * axioms: AxiomsC27.lean queued via lenv-locked.sh (log axioms-c27.log); AxiomsC28.lean to run once EvenRows is built
    (researcher's build_next.sh: EvenContraction, EvenRows still queued at 03:08).
  * even_controls.py positive controls (background) — result to add to C28 finding 3.
  * then: axioms finding + verdicts per check + overall verdict at the end of the report.
- 03:1x C27 axioms clean (axioms-c27.log); N9792 examples compiled.
- 03:15 FOUND: researcher's build of EvenContraction FAILED (scratch/c26/build_next.log; scratch/build-SignedDifferenceSets.EvenContraction.log):
  EvenContraction.lean:331:2 "No goals to be solved" in onGrp_of (split_ifs uses h from context, closes the else branch itself;
  329:17 unused h'). So EvenRows cannot build; C28's Lean is unchecked. Testing fix (drop `with h'` and second bullet) in
  reviews/R29/EvenContractionFix.lean via lenv-locked (log evenfix.log).

## STATE at pause (03:18, researcher asked all agents to pause)
Report so far: reviews/R29/report-2026-11-07-0305.md.
Verdicts per check:
- C27 1 math: SURVIVES. 2 Lean statement: SURVIVES. 3 rows (259, independent recheck, 0/214 exists): SURVIVES.
  4 axioms: SURVIVES (axioms-c27.log, clean). 5 literature: done; note C27 beats Tan's F(m,n) on N9792 (F=10 vs 20) via
  C10's translate; claim wording "This is Schmidt's bound" -> "at least as strong as". C27 overall: SURVIVES.
- C28 1 math: SURVIVES (50 objects/275 quotients). 2 Lean statement: SURVIVES (by reading). 3 rows (8, open, keys,
  independent exhaustive search finds no Z): SURVIVES. 4 axioms: NOT RUN — EvenContraction failed to build
  (331:2 no goals in onGrp_of); researcher says the fix is in progress. 5 literature: done.
  C28 overall now: FLAWED (Lean not building) until the fixed EvenContraction + EvenRows build under --wfail.
Stopped: my lock-waiting compile of EvenContractionFix.lean (killed while waiting; lock owner agentX untouched).
Still running: python even_controls.py (positive controls for even_rows_search, nice 10, 1 thread) — not Lean.
Left after "go":
 1. Once researcher's EvenContraction and EvenRows build clean: run AxiomsC28.lean via lenv-locked.sh
    (the scratch fix test is then unnecessary). Note instance renames (DescentRowCert.instDecidableKills,
    EvenCert.instDecidableOk) do not affect AxiomsC27/C28 files (they don't name instances).
 2. Add even_controls result to C28 finding 3 (must find >=1 vector on nontrivial L for object rows).
 3. Write verdict section at end of report; reply with path + verdicts.
- 03:2x even_controls.py finished: on 24 object rows with nontrivial L (r up to 8, d up to 9) the independent search finds
  >= 4 vectors each (e.g. O13 (32,20,4) r=8: 64; O31 (256,106,42) r=8: 128; O104 (72,48,12) r=4,d=3: 168), including the
  killed rows' own parameters (64,18,2), (64,22,6), (64,46,30) in other groups. Positive control passes. Item 2 of "Left" done.
## After "go" (03:2x)
- Researcher fixed onGrp_of (split_ifs; exact hf — same as my proposed fix); EvenContraction.olean rebuilt 03:20.
  EvenRows was killed by the RAM watchdog; it is being split into EvenRows/NXXXX.lean, and the researcher will say when they're built.
- UnramifiedDescent.lean changed at 02:50 (instance rename to DescentRowCert.instDecidableKills), olean rebuilt 03:24;
  UnramifiedRows.olean is missing (rebuild pending). Rerun the C27 row axioms (AxiomsC27.lean) once it's back.
- Running: AxiomsC28a.lean (EvenContraction + UnramifiedDescent theorem axioms) via lenv-locked, log axioms-c28a.log.
- axioms-c28a.log: all 7 theorems clean (EvenContraction 03:20 build, UnramifiedDescent 03:24 build). Left: per-row EvenRows axioms; C27 rows recheck after UnramifiedRows rebuild.
- 04:30 interim verdicts written to the report (C27 SURVIVES; C28 UNCLEAR pending the row builds). To resume: once the researcher says
  the EvenRows/NXXXX files are built, adapt AxiomsC28.lean to the new module and theorem names (check them with grep) and run it via
  lenv-locked; once UnramifiedRows.olean exists again, re-run AxiomsC27.lean. Then finalize the C28 verdict.
