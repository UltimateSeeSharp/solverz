# C22 refuter running notes (2026-11-06)

## F-rows Row list recomputed independently (`rows.py`, own parser, v_p(0) = inf)
On all 70,543 rows: 464 `open` rows hit, 0 `exists` rows hit (181 exists), 405 Gordon "No" hit, 25,216 Open->none hit
(mostly p = 2 n non-square, He–Wu). Restricted to `r2/target.txt` (11,545): exactly the 905 ids of `sylow_hits.txt`
(set equality both ways); 464 open + 441 none (297 C19, 144 C20) in the current instances.csv. No p >= 11 hit.

## F-consistency Consistency with C17/C19/C20 and other rules
Every row whose instances.csv evidence names C17 (213), C19 (297), C20 (144) is hit by C22 (all 654). C22 depends
only on (v, k, λ) (t = v_p(v) via the full Sylow quotient), so a hit kills every group of that order: no (v, k, λ)
has both a hit row and an `exists` row. No row has n <= 0. Overlap with older rules: C5 32, C7 24, C8 6, C13 52,
C14 223 rows (none-status, consistent).

## F-proof Proof checked step by step (by hand)
1. ψ(a)·σψ(a) = n for ψ ≠ 1 on H: apply ψ to aa⁽⁻¹⁾ = n + λ(v/p^t)H (C3), ψ(H) = 0, ψ(−h) = σψ(h). OK.
2. (p) = (π)^Φ in O = ℤ[ζ_{p^J}], Φ = φ(p^J); σπ = −ζ⁻¹π, so v_π(σx) = v_π(x) and 2v_π(ψ(a)) = Φe exactly.
   Φe even: p odd ⇒ Φ even; p = 2, J ≥ 2 ⇒ Φ even; p = 2, J = 1 ⇒ ψ(a) ∈ ℤ, ψ(a)² = n ⇒ e even. For p = 2, t ≥ 1
   there is always an order-2 character, so n = m² (needed, not only for J = 1). OK.
   The induction form for Lean ("∀x, π^(2b) | xσx ⇒ π^b | x", peel π off x, not off n) is sound.
3. Characters of lower order in ℤ[ζ_{p^j}] ⊂ O: v_{π_J} = p^{J−j}·v_{π_j}, so all have v_{π_J} = Φe/2. OK.
4. z = p^t a₀ − s′ ∈ ℤ, π^(Φe/2) | z ⇒ Φ·v_p(z) ≥ Φe/2 ⇒ v_p(z) ≥ ⌈e/2⌉ ⇒ p^min(t,⌈e/2⌉) | s′. OK (s′ = 0 fine).
5. p = 2: real nontrivial characters: 2^R − 1 (R = 2-rank of H ≥ 1), values ∈ ℤ, = ±m; sum mT, T odd ⇒ v₂ = w = e/2.
   Non-real x = π^a y (a = Φw), σx = (−ζ⁻¹)^a π^a σy, −1 ≡ 1 and ζ ≡ 1, y ≡ σy mod π ⇒ π^(a+1) | x + σx.
   S_nr = p^t a₀ − s′ − mT ∈ ℤ (difference of integers), v_π ≥ a + 1 ⇒ v₂(S_nr) ≥ w + 1.
   So v₂(2^t a₀ − s′) = w exactly. t ≤ w: v₂(s′) < t gives v₂(...) = v₂(s′) < w, contradiction. t > w: v₂(s′) < w gives
   v₂ = v₂(s′) ≠ w; v₂(s′) > w (incl. s′ = 0) gives v₂ ≥ min(t, v₂ s′) > w. Hence min(v₂ s, t) = min(w, t). OK.
6. Stronger-t monotonicity: both forms are implied for smaller t, so the Sylow quotient (t = v_p(v)) is strongest and
   the rule is group-independent. C17's R-form is implied (min(·,R) of an equality at t ≥ R).
No gap found.

## F-objects Every known SDS satisfies C22 and each intermediate claim (`objcheck.py`, `cyc.py`)
`cyc.py`: exact ℤ[ζ_q] arithmetic, v_π by v_p of the norm (Bareiss determinant), self-tested (|N(1−ζ)| = p, v_π(p) = Φ,
1+ζ unit for p odd). On all 58 objects O1–O58 (re-verified as SDS by autocorrelation, O33 of order 4096 excepted) and
the 14 E10 `found` sets: for every p | v, on the Sylow-p quotient H, every ψ ≠ 1 has v_π(ψ(a)) = Φe/2 exactly; real
characters (p = 2) give ±m; every non-real pair has v_π(x + σx) ≥ Φw + 1; Σ_ψ ψ(a) = p^t a₀; v₂(S_nr) ≥ w + 1; the
parameter form holds: 0 violations (`objcheck_objects.out`, `objcheck_e10.out`). Non-trivial cases among them: the
p = 2 equality at t > w with v₂(s) = w (O13–O20, O26–O33, O47–O56: n = 16, 64, 1024 on groups of exponent up to 16),
p = 3, 5, 7 with e = 2 (O7–O11, O40–O46, incl. C₇ × C₄₉). E10 sets have e = 0 (trivial) except nothing.

## F-brute Small cases: 0 violations (`brute_h.py` → `brute_h_big.out`, `products.py` → `products.out`)
Every integer vector on H with constant off-zero autocorrelation and n > 0 (negation-normalized): C₂ [−15,15] (465),
C₃ [−12,12] (7,800), C₄ [−7,7] (516), C₂² [−7,7] (420), C₅ [−6,6] (1,430), C₇ [−3,3] (1,218), C₈, C₂×C₄, C₂³ [−3,3]
(608, 768, 672), C₉, C₃² [−2,2] (342, 1,854): C22's conclusion and n = m² (p = 2) hold for all. Both sides are
attained (e.g. C₂: v₂(s′) = w = 0..4 all occur; C₄: (v₂ s′, w) = (2,3), (3,2), (4,2) ...), so the rule is tight.
Stress where w = e/2 is near or above t: group-ring products of these (closed: (n₁+μ₁H)(n₂+μ₂H) = n₁n₂ + μH), pair
products, 20k triple and 20k quadruple products, each shifted by cH (c ∈ {−2,−1,0,1,3}): 271,820 (C₄), 252,920 (C₂²),
309,720 (C₈), 433,320 (C₂×C₄), 433,320 (C₂³), 394,975 (C₉, base [−2,2]), 207,695 (C₃²), 333,975 (C₅), 644,150 (C₇)
vectors; w from 0 to 9 against t = 2, 3 (every combination t < w, t = w, t > w occurs): 0 violations; the product
identity itself asserted on each.

## F-sds Every SDS on every abelian group of order <= 12 (`sds_small.py` → `sds_small.out`)
Exhaustive over {−1,0,1}^G (16 groups, 952 SDS up to sign, 68 (v,k,λ,G) realized, incl. mixed C₆, C₁₀, C₁₂, C₂×C₆
through their Sylow quotients): C22 holds for every p | v, 0 violations. Only non-nsq hit rows with v <= 32:
(24,18,2) on C₂²×C₆ (C17), C₂×C₁₂ (C19), C₂₄ (Gordon "No", orbit exhaust): consistent.

## F-e8 E8 contraction vectors re-checked with my own parser
`scratch/e8/combined.out` (worktree copy, same size as the main folder's): 61,818 `found` p-group quotients (17,557 of
them the full Sylow quotient), C22 with t = log_p |H|: 0 violations (matches the ideator's count).

## F-junk Lean hazard: v_p(0). s = 0 occurs on 53 `exists` rows (v, v − 1, −1), v = p^a odd
E.g. N1 (5,4,−1) [O4], N2 (9,8,−1) in C₃² [O5], N1327 (81,80,−1): s = 0, p | v, p | n (e = t = a). C22 holds there
(p^min(...) | 0), and row codes treat v_p(0) as ∞ (`sylow.py` 99, mine 10^9). But Mathlib's `padicValNat p 0 = 0`: a
Lean statement written as `min(t, ⌈e/2⌉) ≤ padicValNat p s` (or the p = 2 `min (padicValNat 2 s) t = ...`) is FALSE
on these 53 rows (O4, O5 are Lean-checked SDS) and could not be proved. State it with divisibility:
p odd `p ^ min t ((e+1)/2) ∣ s`; p = 2 `2 ^ min t w ∣ s ∧ (w < t → ¬ 2 ^ (w+1) ∣ s)` with n = m², w = v₂(m).
Also p = 2: e/2 must be v₂(m) with n = m² proved first (ℕ-division e/2 with e odd is junk, vacuous here).

## F-wording Statement wording (minor)
C22's p = 2 line drops "n = m²" (the ideator's B1a has it). As written, "min(v₂(s), t) = min(e/2, t)" is ill-typed for
e odd and, for n non-square with e even (n = 12), is a true-but-weaker statement; the row rule (and the 24,395 `nsq`
rows, He–Wu Thm 4.2) needs the conclusion "n = m² and min(v₂(s), t) = min(v₂(m), t)" for t ≥ 1. Proof gives it (an
order-2 character exists when t ≥ 1). "Contains C17/C19/C20" holds as row sets (checked), and C17 is implied as a
theorem (t ≥ R); C19/C20 are not implied as theorems in general, only on their rows.

## F-lit Literature
Opened: He–Wu arXiv:2608.22936v2 (html): Thm 3.2 self-conjugate p with p ∤ m (m | exp G) ⇒ v_p(n) even; Thm 4.2 v even
⇒ n square (C22's p = 2 `nsq` part); no congruence for s mod p powers, nothing for p | gcd(v, n). Gordon
arXiv:2212.10630 (html): Lemma 1.1 (s integral), λ ≥ −1, Lemma 5.2 intersection numbers; no p-adic result. Turyn 1965
(PJM 15, abstract page only; PDF not readable here): character values in ℤ[ζ_m], divisibility; for DS with n, v even
and v₂(v) ≥ v₂(n)/2, no character of order 2^a (positivity/magnitude based). Two web searches (SDS + p-group quotient
+ (1−ζ); DS + p | v, n + Fourier inversion + exponent bound): no source states C22's congruence for SDS.
Credit: the ingredients are classical (Turyn 1965 self-conjugacy incl. the ramified prime 1 − ζ above p | exp,
Fourier inversion as in Lander/Pott, Ma-type "χ(Y) ≡ 0 mod p^a ⇒ structure" lemmas); the n = m² part is He–Wu Thm 4.2;
the SDS parameter congruence on the Sylow quotient (and its p = 2 equality) was not found in print.

## F-quot Independent kill test on hit rows (`quot_search.py` → `quot_search.out`)
Exhaustive search of integer vectors on every group of order |H| (C₈, C₂×C₄, C₂³ or C₉, C₃²) with Σa = s, Σa² = n + μ,
|a_h| ≤ v/p^t, max at 0, then constant autocorrelation μ. Controls (O21 at p = 3 and p = 2, O23, O25): their coset-sum
vectors are found (120, 6, 120, 120). Hit rows: the 27 smallest of the 163 (|H|, n, μ, s, cap) classes with |H| ∈ {8, 9}
(9 on order 8, 18 on order 9; e.g. N2993 (120,18,2), N1606 (90,85,4), N2899 (117,109,1)): no vector on any group.
Stopped after 27 classes for time (~1–3 min per class in pure Python).
