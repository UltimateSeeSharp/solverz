# Refuter notes: I16 lift search (helper L)
Started 2026-11-07. Brief: scratch/refuter-not-kept/lift-brief.md.
- b3.out, axioms.out, Part01 build log: not present at start.
- LiftSearch.lean 1-250 read (phase 1 cover = VectorSearch.go with leaf `L.contains`).
- 08:20 Read all of LiftSearch.lean. Soundness chain is kernel-proved: cover_sound/mem_of_cover (phase 1),
  liftGo_false (cut never removes the key-least image; accOK via abs_corr_sub_le; lex cut via keyL),
  exists_min over Reach (closure of maps, so minimality vs every generator), sol_act (affine, coset-fixing),
  false_of_liftRow, not_hasSDS_of_lift (sum = +-s by negation; translate so |b_0| max). No gap found by reading.
- N70 statement: `n70_not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 17 4`, s = 11 (121 = 17 + 4*26). Key matches instances.csv.
- Build state at 08:18: LiftSearch build log (08:01) FAILED --wfail on `show` linter; file edited 08:02 (`change`);
  Tests log (08:04) failed on privateModule linter; Tests edited 08:05. No later build log yet; lock held by researcher.
  b3.out / axioms.out absent. -> rows not settled until the b3 chain (or my rerun) passes.
- Next: own engine reviews/R32/eng.py (numpy BFS coset by coset, no symmetry, own vector enumeration).
- 08:30 eng.py validated: (9,8,-1) in C3^2 all-vector mode finds 54 SDS = brute force 54 (brute9.py);
  N73 (27,17,8) found at once. N70: 144 vectors with sum +11, 16 translation reps (= L's 16 classes),
  3.05M BFS nodes, no SDS (5.8 s). runall.sh (N70 all 144 vectors, N76, N77, N137, N130, N134-6, N138) -> runall.out.
- Literature: He-Wu arXiv:2608.22936 already applied by import (README); N70 still open after it.
- 08:45 runall: N70 all 144 vectors (no symmetry at all) 27.5M nodes, 0 SDS; N76 0 (266k); N77 0 (328k);
  N137 control found. valid.out: Gordon Yes rows N19 [3,6]/[3,3], N31 [20]/[10] found; No rows N20 (two
  quotients), N33, N12, N13, N36, N11 none. Generator stats on N73 (gen-n73.out) asserts "lift found" -> not killed.
- runall done: N134 0 (752k nodes), N135 0 (752k), N136 0 (756k), N138 0 (759k), all with 64 vectors of sum +20,
  8 translation reps on H = C2^3. N130 control killed by hand at 5.4 GB (BFS blow-up), not rerun.
- Waiting for L's chain (axioms.out, b3.out); lock held by researcher's big HalfRows builds.
- N70Axioms.lean prepared (run after Part01 builds: sh scratch/lenv-locked.sh refuter problems/signed-difference-sets/reviews/R32/N70Axioms.lean)
- 08:55 L's chain done: Tests.LiftSearch and LiftRows.Part01 built --wfail clean (1577 s, 4.32 GB); generic axioms clean. Running N70Axioms.lean.
- 09:00 n70 axioms clean; report written (verdict SURVIVES).
