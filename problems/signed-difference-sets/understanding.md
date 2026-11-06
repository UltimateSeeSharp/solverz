# Understanding

**Holds.**
- Gordon's table has 70,543 rows (`instances.csv`); He–Wu's four obstructions and three
  constructions leave 22,459 open (README, reproduced by the importer).
- Rules on the parameters settle most open rows, each one Lean theorem plus one kernel check
  over its rows: self-conjugacy on quotients and its moments/box forms (C5, C13, C14), support
  parity (C8), marked counts (C7), multipliers with a verified orbit search (C15, I5), and
  character sums on p-group quotients (C17, C19, C20). 11,357 rows settled in Lean on
  2026-11-06; the table is 84.3% settled (journal). The rules are classical (Turyn,
  McFarland/Gordon Thm 5.1, the weighing-matrix parity bound), newly applied to the table.
- The character rules on 2- and 3-groups are cases of one valuation congruence at the prime
  above p (C22, heuristic until its refuter reports): exponents 2, 3, 4 need only ℤ, ℤ[ω],
  ℤ[i] as integer pairs; higher exponents need cyclotomic integers. Ma's lemma extends it to
  mixed quotients C_{p^j} × K (C21, open).
- "Open" often means "never searched": exhaustive and orbit searches found sets for 16 of
  the 41 open rows with v ≤ 40 they finished (E4, E7), and E10 found 5 more (O34–O38).
- Signed combinations of relative difference sets give SDSs (C18, I15): R − N, G − R − N,
  G − 2R − N, G − R − 2N for semiregular and affine RDS; 19 open rows (O40–O58), and valid
  sets where the database's stored ones fail (O59, O60). Partial difference sets with
  λ′ − μ = 2 give more (C11, I7).
- "Open" is not enough for a Solution: the database lags the papers (12 rows a published
  construction settles, refuter db-lags) and some of its labels lack a valid witness
  (state.md, Needs the user). Every proposed row is first checked against Gordon, He–Chen–Ge
  and He–Wu.
- The kernel's memory is per declaration: one kernel check over many cases is split into
  declarations (N58470's set check: 8.9 GB in one, 3.4 GB in eight; `SetCheckSplit`), and
  Lean runs one process at a time (state.md, Resources).
**Blocks.** Nothing counts until Lean checks it. C9 is in Lean for squarefree n only (C15);
the E10/E11 `none` rows with n not squarefree (1,992) wait on it (I13). 322 I5 rows need
more search leaves than a kernel check affords. After I11–I15 about 7,000 open rows have no
method (ideator round 2): 2,522 with gcd(v, n) = 1 whose orbit search E10/E11 cut, 4,475 with
gcd(v, n) > 1 where no multiplier theorem applies, 1,803 of them with a non-cyclic Sylow
subgroup where Ma's form fails.
**So a Solution must.** Per row: a set Lean checks, or a rule's Lean theorem plus its
Lean check for that row; and, before it is proposed, a check against the known
constructions of Gordon, He–Chen–Ge and He–Wu.
