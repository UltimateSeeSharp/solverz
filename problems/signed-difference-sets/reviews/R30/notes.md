# C25 refuter notes (2026-11-07)
- Read brief, C25.md, agentY progress, MultiplierSelfConj.lean, CosetSearchSelfConj.lean.
- keys.py: all 26 row theorems (Parts 95-98) match instances.csv keys (group factors, k, lam), all `open`, = targets.tsv.
- objtest.py (independent of a7selfconj.py): on all 104 known SDS objects, 140 product quotients with gcd(|H|,n)=1;
  M' (Lean's per-prime condition) strictly bigger than C10's group on 14; C25's conclusion (one translate fixed by all
  of M') holds on all 140, 0 failures.
- indep.py (own DFS, no solver code; constraints: orbit-constant under t, |a|<=c, sum=s, sum sq=n+lam c, marked-count
  bounds/parity, full autocorrelation): all 26 rows 0 survivors, even WITHOUT C5's filter (max 34 s/row).
- Lean check (Check.lean: axioms of all 26 rows + C25 + wrappers, statement pins vs HasSDS, C25 => C10) queued
  via lenv-locked.sh -> reviews/R30/check.out.
- Lit: Miller arXiv:2511.10231 (html) Thm 7: for p | n1 either p self-conj mod v* (q-free parts) or t = p^j mod
  v*/p^nu; then t multiplier if n1/gcd(n1,v) > lam or gcd(v, M~) = 1; Miller calls it a variant of Thm 3.1 of the
  Gordon-Schmidt multiplier survey (Section 3 "The Multiplier Theorem of Leung, Ma, and Schmidt"); proof omitted.
  No even-valuation condition there (C25.md has none either; Lean adds it: weaker, sound).
- exists.py: 214 exists rows; 60 have a quotient (|H|<=150, gcd(|H|,n)=1, M' nontrivial): 145 (row,H) pairs the
  DFS finds a vector (rule does not fire), 12 capped at 3M nodes (inconclusive), 0 killed. 154 rows no quotient.
- lit done (Miller html Thm 7; Gordon-Schmidt survey Thm 3.1 (ii); Gordon SDS paper Thm 5.1 = C10 form).
- report: header, check 4a keys, 6 lit, 1 math, 2 statement, 3 predicates written. Pending: Lean check.out,
  posctl output, then 4b (indep kills + controls), 5 (axioms), verdict.
- posctl.py: 189 pass, 0 fail, 53 capped. Lean Check.lean: all clean. Report finished: SURVIVES.
