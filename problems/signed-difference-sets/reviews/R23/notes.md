# Round 5 refuter notes (C21 in Lean + 1,457 rows), started 2026-11-06

Restatement: MaRule (MaRule.lean) says: for finite abelian G, K, prime p, r > 0, i > 0, a surjection
G ->+ ZMod (r p) x K, |G| = c |H|, p^i x = -x on K, p^e | k - lam, k != lam, 2b <= e, 2c < p^b, and the
cyclotomic facts at (p, r) in every commutative ring, there is no SDS (|G|, k, lam) on G. Rows: each
part's list of (Row, MaRowCert); Kills is decided by the kernel; All.lean applies maRule.

## F-rows (part 3): rows re-derived independently, exact match
`rows5.py` (mine; `rows5.out`): my own parser of instances.csv and my own rule (for each prime p with
e = v_p(k − λ) ≥ 2: j = max p-exponent of the factors, K = the largest quotient of the p'-part of exponent m over all
m | exp with some i ≥ 1, p^i ≡ −1 mod m; fire when 2c < p^⌊e/2⌋). Result: 4,607 hits (3,150 none, 1,457 open,
0 exists). My 1,457 open hits = the parts' 1,457 ids exactly (both differences empty). Each part entry's
(id, ms, k, λ) equals its instances.csv key (0 mismatches, factor order included); all 1,457 are `open` now.
My re-implementation of `Kills` (plus "r is a power of p") accepts all 1,457 certificates. settle-c21.tsv: 1,457
unique ids, = the parts' set, each line's part name and theorem name match the part the row sits in (0 mismatches).
No object's Instance is in the batch; `objs5.py`: all 60 objects re-verified as SDSs by my autocorrelation, and my
rule fires on none of them.

## F-stmt (part 1): MaRule says C21 (with r forced to p^(j−1)); no hypothesis is weaker than C21 allows
Read against claims/C21.md, hypothesis by hypothesis (MaRule.lean lines 20-28):
- quotient `ZMod (r p) × K`, φ surjective: H = C_{rp} × K. r is free in the binder, but the last hypothesis
  (CycloFacts p r) is false unless r is a power of p: if a prime q ≠ p divides r, take S = ℤ[ζ_{rp}], x = ζ_{rp};
  x^r is a primitive p-th root, so Ψ(x) = 0, but rp is not a prime power, so x − 1 is a unit and (x − 1)^N = p z
  would make p a unit. So MaRule's instances are exactly C21's H = C_{p^j} × K, r = p^(j−1). At r = p^(j−1),
  Ψ = Φ_{p^j} and p = (1 − ζ)^φ·unit in ℤ[ζ_{p^j}], so the facts hold in the universal ring ℤ[X]/(Ψ), hence everywhere.
- `∀ x : K, p^i • x = −x`, i > 0: ⇔ p^i ≡ −1 mod exp K; forces p ∤ |K| (orders divide p^i + 1). K = 1 allowed. Same
  as C21 ("for some i", i = 0 adds nothing).
- `(p:ℤ)^e ∣ k − λ`, `2b ≤ e`: weaker in form than e = v_p(n), b = ⌊e/2⌋, but any such (e, b) has b ≤ ⌊v_p(n)/2⌋, so
  2c < p^b implies C21's p^⌊v_p/2⌋ > 2c. Not more general.
- `k ≠ λ`: needed (p^e ∣ 0 for every e); C21 gets it from e = v_p(n) ≥ 2. Present.
- `card G = c · card H`, `2c < p^b`: c = v/|H| exactly; strict, as C21 (CW(4,4) in C4 sits at equality).
  c ≥ 1 since |G| ≥ 1, so b ≥ 1 and e ≥ 2 are implied.
- Conclusion `¬ HasSDS G k lam` with the problem's own HasSDS (Statement.lean; no shadowing definition of
  HasSDS/IsSDS/Grp/Row/MaRule/CycloFacts in the 20-file import closure).
Classical check of truth (independent of the Lean proof): Turyn (Tan v4 Result 2.6) gives p^b | χ(Y) for every
non-trivial χ of H (YȲ = n + λcH, p self-conjugate mod the p-free part exp K of exp H); Ma (Result 2.7, H has
cyclic Sylow p) gives Y = p^b X1 + P X2; coefficients of Y lie in [−c, c], so (1 − g)Y has entries ≤ 2c < p^b,
hence 0, so Y = P·Z and χ(Y) = 0 for χ non-trivial on P, against |χ(Y)|² = n ≠ 0. So MaRule is a true statement.
Concrete test: all 60 objects and all 200 `exists` rows: my maximal rule (best j, best K over all self-conjugate
exponents, best b) fires on none.

## F-kills (part 2): Kills is only a sufficient check; every MaRule hypothesis is derived in a kernel-checked theorem
`MaCheck.lean` 41-71: `not_hasSDS_of_maRule` builds φ = linMap (surjective by `linMap_surjective` from the
preimages), card G = (ms.prod / (r p ks.prod)) · card H with `Nat.div_mul_cancel hprod` (the floor division is exact
because Kills has `r p ks.prod ∣ ms.prod`), p^i x = −x from `(p^i + 1) • x = 0` (`Grp.nsmul_eq_zero`, each factor
d ∣ p^i + 1), and passes the strict `2 c < p^b`, `k ≠ λ`, `2b ≤ e`, `p^e ∣ k − λ` unchanged. `ks ≠ []` only
selects the `Grp (k₀ :: ks)` shape ([1] = trivial K; a 0 factor is impossible since d ∣ p^i + 1). A wrong Kills
could only make that theorem unprovable, not unsound. My re-implementation of Kills (rows5.py `kills`) agrees on
all 1,457 certificates, and adds r = p-power: true for all. Unused conjunct `∀ m ∈ ms, 0 < m` is harmless.

## F-cyclo (part 4): CycloFacts.mul and the 25 pairs
Statement (PolyCert.lean 159-160): p prime, 2 ≤ (p − 1) r, CycloFacts p r → CycloFacts p (p r). True (p-powers go to
p-powers; for other r the premise is false, F-stmt), and kernel-proved. The rows use exactly the 25 pairs of
`maPairs` (my parse of the six parts): (2, 1..128), (3, 1..81), (5, 1..25), (7, 1..49), (11, 1/11), (13, 1/13),
(17, 1), (19, 1). Each is a base `MaCert` at r = 1 (and (2, 2), because (2 − 1)·1 < 2 blocks mul from (2, 1)) or a
mul chain from one (Polys.lean 29-224); `part0N_kills` also decides `(p, r) ∈ maPairs`. Hand check of the (2, 1)
certificate: −(x − 1) + (1 + x) = 2 and x − 1 = 2(−1) + (1 + x)·1.

## F-axioms (part 5): standard axioms only; no forbidden tokens
`R5Check.lean` (run via lenv-locked.sh, `R5Check.out`): `#print axioms` gives [propext, Classical.choice, Quot.sound]
for maRule, not_hasSDS_of_mem_part01 … part06, not_hasSDS_of_mem_maRows, CycloFacts.mul,
cycloFacts_of_mem_maPairs; part03_kills: [propext, Quot.sound]. Grep of the 20-file import closure of
MaRows/All.lean for sorry, native_decide, axiom, implemented_by, extern, ofReduceBool, trustCompiler, unsafe,
opaque, admit, debug./skipKernel, elab/macro/syntax, other set_option: no hit (only maxRecDepth).

## F-olean (parts 3, 5): the built library holds exactly instances.csv's rows; per-instance statements check
The MaRows sources (mtime 21:46:34) are newer than their oleans (21:41); U's notes say the generator was rerun
("reproducible"), and `regen5.py` (marows.py redirected into round5/gen) reproduces all 8 files byte for byte.
In R5Check.lean, kernel-checked: for each part, `partNN.map (id, ms, k, lam) = <list I generated from
instances.csv>` (all 1,457, in part order), and 6 per-instance statements in the plain types, e.g.
`¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 18) 107 26` (N21780), `¬ HasSDS (ZMod 2 × ZMod 246) 300 44`
(N68502), `¬ HasSDS (ZMod 60) 35 10` (N571), N168, N930, N7151, each from not_hasSDS_of_mem_partNN: no error.
The batch has no λ < 0 row and no λ = 0 row.

## F-small (part 1, extreme cases): every SDS of order <= 12, and C16 at n = 16
`small5.py` (`small5.out`): all 3^v sign vectors in all 16 abelian groups of order 2..12, plus C16 with k >= 15
(λ >= −1 forces k >= 15 when n = 16). My rule fires on 14 (group, k, λ): C9 (8, −1), (9, 0); C12 and C2 × C6
(8, −1) … (12, 3); C16 (15, −1), (16, 0). None has an SDS. It fires on no existing SDS; (9, 8, −1) exists in C3 × C3
(N2) and the rule fires only in C9, where none exists; CW(4, 4) in C4 sits at 2c = p^b and is not hit.

## Literature (2026-11-06)
- Opened: Tan, Group Invariant Weighing Matrices, arXiv 1610.01914 v4 HTML: Result 2.6 (Turyn: X X̄ ≡ 0 mod t^{2b},
  t self-conjugate mod v ⇒ X ≡ 0 mod t^b), Result 2.7 (Ma: cyclic Sylow p, p^a | χ(Y) for all non-trivial χ ⇒
  Y = p^a X1 + P X2). Matches the citation in claims/C21.md (v1 numbers them 2.13 / 2.15). With these two the
  classical proof of C21 is three lines (F-stmt), so MaRule is a known-true statement.
- Search "Ma's lemma cyclic Sylow p-subgroup … weighing matrix": NTU weighing23.pdf and the AJC v18 p111 OCR and
  Arasu–Ma JACO 14 were listed; the NTU PDF could not be decoded here (not read). Nothing found that states C21
  for SDSs; credit as in the c21 report (Ma 1985, Turyn 1965; mixed-quotient SDS form ours).
- The batch has no λ = 0 row, so no overlap with the open CW(n, k) of Arasu–Gordon–Zhang / Tan 2026.

## F-olean addendum: built definitions = committed sources; controls fail as they must
`R5Source.lean` (`R5Source.out`), kernel-checked: `partNN = <the source's list literal>` for all six parts, each of
the 27 polynomial lists of Polys.lean = its source literal, `maPairs` = its literal: no error. Controls in the same
run fail as they must: `¬ HasSDS (ZMod 60) 36 10` from N571's entry (type mismatch, k = 35), and N571 with λ = 11
(membership decided false). R5Control.lean: part06's row list with one λ changed (44 → 45) is rejected.
