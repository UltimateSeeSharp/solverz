# refuter xsplit notes (2026-11-07)

- 06:11 start. parts.log: built clean 60-71; Part72 KILLED by watchdog (83 s, 4.0 GB free), loop "stopped at 72".
  Rows in built parts: N363 (60), N71 (62), N1512 (63), N7332 (67). Not built: N9513 (73), N13357 (85),
  N3958 (104), N13285 (127), Part128-137.
- Reading: OrbitSearchSplit.lean (404 lines), Tests, Part60. Wrappers pass ⟨h1..h6, hex⟩ to verified
  not_hasSDS_of_orbitRow(') so OrbitRowHyps must match OrbitRow conjunct-for-conjunct (type-checked).
- 06:25 rows.py (own parser, output rows.json): 38 row theorems + 2,346 slice theorems in Part60-137, all parsed
  (count of `theorem` = parsed), 0 mismatches: statement group = ms = key factors, k/λ = key, t/s same in both
  places, s² = k+λ(v−1), gcd(v,n)=gcd(t,v)=1, t ≡ p^f on every factor, rule C15 iff n squarefree, chain = slice0..N−1,
  slice params = row's, cuts contiguous from 0, slices never in a later part; imports only OrbitSearchSplit + parts;
  options only maxRecDepth/Elab.async. No row `exists` or with an object.
  NOTE: 5 of the 30 batch2 rows are already `none` by C27/UnramifiedRows (N31876, N15437, N32197, N31825, N45850):
  only 25 batch2 rows are still open (bookkeeping, redundant Lean work, not an error).
- Wrappers/defs: single def of HasSDS (Statement.lean), orbitExhaust (OrbitSearch.lean 479); OrbitRowHyps(') are
  passed as ⟨h1..⟩ into not_hasSDS_of_orbitRow(') with hex, so type checker enforces conjunct match. grep: no
  axiom/opaque/native_decide/implemented_by/extern/unsafe/sorry in OrbitSearchSplit, its Tests, Part60-137.
- 06:40 Builds: Part60-71 oleans newer than sources and logs, logs 0 error/warning/sorry, Part67 log "Build completed
  successfully"; lean-build.ps1 runs `lake build --wfail`. Part72 killed (no olean). Root imports neither
  OrbitSearchSplit nor Part60+ (same precondition as i13 #6).
- search.py (own engine: itertools elements, own orbits, orbit order by size desc, suffix-reach pruning, batched
  FFT autocorrelation at every exact-count leaf). Validated: FOUND on N6 (11,6,1) t5, N24 (19,10,3) t7, O69
  (51,19,3) t2; leaves N898 91, N486 48 (= Tests docstrings), N363 1,820 (= helper X), all none.
  Background: all 38 rows single-t (args.txt -> search-t.out).
- 06:55 search-t.out: all 38 rows none with the rows' own t (leaves: N71 38,160 = helper X; N1512 9,696; N7332 23,360;
  N9513 48,834; N13357 63,368; N3958 106,728; N13285 120,432; batch2 1,512-8,637 = helper X's range). Product-group
  control N352 (49,33,1,[7,7]) t=2: FOUND 224 of 1,441,440 leaves. front.py: Lean-order frontier at depth 10 =
  17,562 nodes, a solution under node 95. Lean check queued: reviews/R31/Axioms.lean -> axioms.out.
  Report started: report-2026-11-07-0700.md (findings 1, 2 written).
- 07:05 Lean check queued on the lock (agentV CosetRows Part23 holds it); waiter task b3al6cabj. Findings 3-4 in report.
- 06:59 axioms.out: all module theorems and n363, n71, n1512, n7332 only [propext, (Classical.choice,) Quot.sound];
  #check statements as expected; Grp [88] = ZMod 88 etc. by rfl; N352 controls pass (top 17,562 true, 17,561 false,
  slice 95-96 false). Part73 built 06:43 clean (n9513); axioms73 queued.
- 07:37 axioms73 clean (n9513). Report complete: report-2026-11-07-0700.md. Overall SURVIVES.
