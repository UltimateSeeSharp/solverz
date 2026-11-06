module

public import SignedDifferenceSets.GaussChars

/-!
# Eisenstein characters on a quotient of exponent 3 (C20)

On a quotient `H` with `3h = 0` every character takes values in `{1, ω, ω²}`, so
`ψ(D) = A + B ω` with integers `A`, `B` and `A² − AB + B² = k − λ` for `ψ ≠ 0`. The trace
`ψ(D) + conj ψ(D) = 2A − B` is the same for `−ψ`, and no `ψ ≠ 0` has `−ψ = ψ`, so the nontrivial
characters pair off: `|H| a₀ = s' + Σ (2A − B)` over `(|H| − 1)/2` pairs, `s' = ±s`. A row dies
when for both `s'` the residue `0` is not reachable mod `|H|` (`EisKills`).
-/

@[expose] public section

open ComplexConjugate

namespace SignedDifferenceSets

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] {k : ℕ} {lam : ℤ}
  {D : G → SignType}

/-! ### The cube root of unity -/

/-- `ω = e^(2πi/3) = −1/2 + (√3/2) i`. -/
noncomputable def eisOmega : ℂ := ⟨-1 / 2, √3 / 2⟩

theorem eisOmega_sq_add : eisOmega ^ 2 + eisOmega + 1 = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine Complex.ext ?_ ?_ <;> simp only [eisOmega, sq, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.zero_re,
    Complex.zero_im]
  · linear_combination (-1 / 4 : ℝ) * h3
  · ring

theorem conj_eisOmega : conj eisOmega = -1 - eisOmega := by
  apply Complex.ext <;> norm_num [eisOmega]

theorem eisOmega_ne_one : eisOmega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [eisOmega] at this

theorem neg_one_sub_eisOmega_ne_one : -1 - eisOmega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [eisOmega] at this

theorem neg_one_sub_eisOmega_ne : -1 - eisOmega ≠ eisOmega := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  simp only [eisOmega, Complex.sub_im, Complex.neg_im, Complex.one_im] at h1
  linarith

/-- A cube root of unity is `1`, `ω` or `ω² = −1 − ω`. -/
theorem pow_three_cases {z : ℂ} (hz : z ^ 3 = 1) :
    z = 1 ∨ z = eisOmega ∨ z = -1 - eisOmega := by
  have h : (z - 1) * ((z - eisOmega) * (z - (-1 - eisOmega))) = 0 := by
    linear_combination hz - (z - 1) * eisOmega_sq_add
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h))

/-! ### Values on a group of exponent 3 -/

open scoped Classical in
/-- `A` in `ψ h = A + B ω` for `ψ h ∈ {1, ω, −1 − ω}`. -/
noncomputable def charEisA (ψ : AddChar H ℂ) (h : H) : ℤ :=
  if ψ h = 1 then 1 else if ψ h = eisOmega then 0 else -1

open scoped Classical in
/-- `B` in `ψ h = A + B ω`. -/
noncomputable def charEisB (ψ : AddChar H ℂ) (h : H) : ℤ :=
  if ψ h = 1 then 0 else if ψ h = eisOmega then 1 else -1

theorem charEisA_add_charEisB (h3 : ∀ h : H, 3 • h = 0) (ψ : AddChar H ℂ) (h : H) :
    (charEisA ψ h : ℂ) + charEisB ψ h * eisOmega = ψ h := by
  have h1 : ψ h ^ 3 = 1 := by rw [← AddChar.map_nsmul_eq_pow, h3, AddChar.map_zero_eq_one]
  rcases pow_three_cases h1 with e | e | e
  · simp only [charEisA, charEisB, e, ↓reduceIte]
    push_cast
    ring
  · simp only [charEisA, charEisB, e, eisOmega_ne_one, ↓reduceIte]
    push_cast
    ring
  · simp only [charEisA, charEisB, e, neg_one_sub_eisOmega_ne_one, neg_one_sub_eisOmega_ne,
      ↓reduceIte]
    push_cast
    ring

/-- `A` in `ψ(D) = A + B ω`. -/
noncomputable def charSumEisA (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  ∑ x, (D x : ℤ) * charEisA ψ (φ x)

/-- `B` in `ψ(D) = A + B ω`. -/
noncomputable def charSumEisB (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  ∑ x, (D x : ℤ) * charEisB ψ (φ x)

theorem charSum_eq_eis (h3 : ∀ h : H, 3 • h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) :
    charSum φ D ψ = (charSumEisA φ D ψ : ℂ) + charSumEisB φ D ψ * eisOmega := by
  simp only [charSum, charSumEisA, charSumEisB, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← charEisA_add_charEisB h3 ψ (φ x)]
  ring

/-- The trace `ψ(D) + conj ψ(D) = 2A − B`. -/
noncomputable def charSumTr (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  2 * charSumEisA φ D ψ - charSumEisB φ D ψ

theorem charSumTr_cast (h3 : ∀ h : H, 3 • h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) :
    (charSumTr φ D ψ : ℂ) = charSum φ D ψ + conj (charSum φ D ψ) := by
  rw [charSum_eq_eis h3, charSumTr]
  simp only [map_add, map_mul, map_intCast, conj_eisOmega]
  push_cast
  ring

/-- `−ψ` has the same trace as `ψ`. -/
theorem charSumTr_neg [Finite H] (h3 : ∀ h : H, 3 • h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) : charSumTr φ D (-ψ) = charSumTr φ D ψ := by
  have h := charSumTr_cast h3 φ D (-ψ)
  rw [charSum_neg, Complex.conj_conj, add_comm, ← charSumTr_cast h3] at h
  exact_mod_cast h

/-- C20 (a): on a group of exponent 3, `A² − AB + B² = k − λ` for a nontrivial character. -/
theorem IsSDS.charSumEis_norm [Finite H] (hD : IsSDS k lam D) {φ : G →+ H}
    (hφ : Function.Surjective φ) (h3 : ∀ h : H, 3 • h = 0) {ψ : AddChar H ℂ} (hψ : ψ ≠ 0) :
    charSumEisA φ D ψ ^ 2 - charSumEisA φ D ψ * charSumEisB φ D ψ + charSumEisB φ D ψ ^ 2 =
      k - lam := by
  have h := hD.charSum_mul_conj hφ hψ
  rw [charSum_eq_eis h3] at h
  simp only [map_add, map_mul, map_intCast, conj_eisOmega] at h
  have h' : ((charSumEisA φ D ψ ^ 2 - charSumEisA φ D ψ * charSumEisB φ D ψ +
      charSumEisB φ D ψ ^ 2 : ℤ) : ℂ) = ((k - lam : ℤ) : ℂ) := by
    push_cast
    linear_combination h + (charSumEisB φ D ψ : ℂ) ^ 2 * eisOmega_sq_add
  exact_mod_cast h'

/-- C20 (b): the traces add up to `2 |H| a₀`. -/
theorem sum_charSumTr [Fintype H] [DecidableEq H] (h3 : ∀ h : H, 3 • h = 0) (φ : G →+ H)
    (D : G → SignType) :
    ∑ ψ : AddChar H ℂ, charSumTr φ D ψ = 2 * Fintype.card H * contract φ D 0 := by
  have h := sum_charSum φ D
  have hneg : ∑ ψ : AddChar H ℂ, charSum φ D (-ψ) = ∑ ψ, charSum φ D ψ :=
    Equiv.sum_comp (Equiv.neg _) _
  have h1 : ((∑ ψ : AddChar H ℂ, charSumTr φ D ψ : ℤ) : ℂ) =
      ((2 * Fintype.card H * contract φ D 0 : ℤ) : ℂ) := by
    push_cast
    simp only [charSumTr_cast h3, ← charSum_neg, Finset.sum_add_distrib, hneg, h]
    ring
  exact_mod_cast h1

/-- No nontrivial character of a group of exponent 3 is its own negative. -/
theorem neg_ne_self_of_three (h3 : ∀ h : H, 3 • h = 0) {ψ : AddChar H ℂ} (hψ : ψ ≠ 0) :
    -ψ ≠ ψ := by
  intro hneg
  refine hψ (AddChar.ext _ _ fun h => ?_)
  have hh : -(h + h) = h := by
    have : h + (h + h) = 0 := by rw [← h3 h]; abel
    exact (eq_neg_of_add_eq_zero_left this).symm
  have e : ψ h * ψ h = ψ h * 1 := by
    calc ψ h * ψ h = ψ (h + h) := (AddChar.map_add_eq_mul ψ h h).symm
      _ = (-ψ) (h + h) := by rw [hneg]
      _ = ψ h := by rw [AddChar.neg_apply, hh]
      _ = ψ h * 1 := (mul_one _).symm
  have hne : ψ h ≠ 0 := by
    have := AddChar.map_add_eq_mul ψ h (-h)
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  rw [AddChar.zero_apply]
  exact mul_left_cancel₀ hne e

/-! ### Traces and residues -/

/-- The least `i ≥ i₀` with `n ≤ i²` found within `f` steps, else `n`. -/
def sqrtUp (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => n
  | f + 1, i => if n ≤ i * i then i else sqrtUp n f (i + 1)

theorem le_sqrtUp (n : ℕ) : ∀ f i : ℕ, n ≤ sqrtUp n f i * sqrtUp n f i
  | 0, _ => Nat.le_mul_self n
  | f + 1, i => by
    unfold sqrtUp
    split_ifs with h
    · exact h
    · exact le_sqrtUp n f (i + 1)

/-- A bound `M` with `4n ≤ M²`. -/
def eisBound (n : ℕ) : ℕ := sqrtUp (4 * n) (4 * n + 1) 0

/-- The `t ≤ M` with `t² + 3b² = 4n` for some `b ≤ M` (`M = eisBound n`), in `ℕ` for the
kernel. -/
def eisTracesNat (n : ℕ) : List ℕ :=
  (List.range (eisBound n + 1)).filter fun t =>
    (List.range (eisBound n + 1)).any fun b => t * t + 3 * (b * b) == 4 * n

/-- The traces `2A − B` of the `A + B ω` of norm `n`: `±t` for `t ∈ eisTracesNat n`. -/
def eisTraces (n : ℤ) : List ℤ := (eisTracesNat n.toNat).flatMap fun t : ℕ => [(t : ℤ), -t]

theorem mem_eisTraces {n A B : ℤ} (h : A ^ 2 - A * B + B ^ 2 = n) : 2 * A - B ∈ eisTraces n := by
  set t := 2 * A - B with ht_def
  have ht : t ^ 2 + 3 * B ^ 2 = 4 * n := by rw [← h, ht_def]; ring
  have hn : 0 ≤ n := by nlinarith [sq_nonneg t, sq_nonneg B]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have key : t.natAbs * t.natAbs + 3 * (B.natAbs * B.natAbs) = 4 * n := by
    have : ((t.natAbs * t.natAbs + 3 * (B.natAbs * B.natAbs) : ℕ) : ℤ) = ((4 * n : ℕ) : ℤ) := by
      push_cast
      rw [abs_mul_abs_self, abs_mul_abs_self]
      linear_combination ht
    exact_mod_cast this
  have hM := le_sqrtUp (4 * n) (4 * n + 1) 0
  have h1 : t.natAbs * t.natAbs ≤ eisBound n * eisBound n :=
    le_trans (by rw [← key]; exact Nat.le_add_right _ _) hM
  have h2 : B.natAbs * B.natAbs ≤ eisBound n * eisBound n :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 3))
      (by rw [← key]; exact Nat.le_add_left _ _)) hM
  have i1 := Nat.mul_self_le_mul_self_iff.1 h1
  have i2 := Nat.mul_self_le_mul_self_iff.1 h2
  unfold eisTraces eisTracesNat
  rw [Int.toNat_natCast, List.mem_flatMap]
  refine ⟨t.natAbs, List.mem_filter.2 ⟨List.mem_range.2 (Nat.lt_succ_of_le i1),
    List.any_eq_true.2 ⟨B.natAbs, List.mem_range.2 (Nat.lt_succ_of_le i2), beq_iff_eq.2 key⟩⟩,
    ?_⟩
  rcases Int.natAbs_eq t with e | e
  · exact List.mem_cons.2 (Or.inl e)
  · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 e))

/-- The kill condition of C20 for a quotient of order `N`, sign sum `±s` and `n = k − λ`:
`0` is not reachable mod `N` from `s'` by `(N − 1)/2` traces of norm `n`. -/
def EisKills (N : ℕ) (s n : ℤ) : Prop :=
  ∀ s' ∈ [s, -s], (0 : ℤ) ∉ reachMod N (eisTraces n) ((N - 1) / 2) [s' % N]

instance instDecidableEisKills (N : ℕ) (s n : ℤ) : Decidable (EisKills N s n) := by
  unfold EisKills; infer_instance

/-- C20: no SDS when `s² = k + λ(v − 1)` and a quotient of exponent 3 passes `EisKills`. -/
theorem not_hasSDS_of_eisensteinChars [Fintype H] {φ : G →+ H}
    (hφ : Function.Surjective φ) (h3 : ∀ h : H, 3 • h = 0) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((Fintype.card G : ℤ) - 1))
    (hkill : EisKills (Fintype.card H) s (k - lam)) : ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  set N := Fintype.card H with hN
  have hs' : (∑ x, (D x : ℤ)) ∈ [s, -s] := by
    have h := hD.sum_sq
    rw [← hs] at h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h <;> simp [h]
  set T := charSumTr φ D
  have hT0 : T 0 = 2 * ∑ x, (D x : ℤ) := by
    simp [T, charSumTr, charSumEisA, charSumEisB, charEisA, charEisB, Finset.mul_sum]
  set E := Finset.univ.erase (0 : AddChar H ℂ)
  obtain ⟨l, hllen, hlmem, hlsum⟩ := exists_pair_list T (charSumTr_neg h3 φ D) E
    (fun ψ hψ => Finset.mem_erase.2 ⟨neg_ne_zero.2 (Finset.ne_of_mem_erase hψ),
      Finset.mem_univ _⟩)
    (fun ψ hψ => neg_ne_self_of_three h3 (Finset.ne_of_mem_erase hψ))
  have hEcard : E.card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq]
  have hN1 : 1 ≤ N := Fintype.card_pos
  have htot : ∑ ψ, T ψ = 2 * N * contract φ D 0 := sum_charSumTr h3 φ D
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar H ℂ)), hT0, ← hlsum] at htot
  have hhalf : ∀ y ∈ l, 2 * (y / 2) = y := by
    intro y hy
    obtain ⟨ψ, -, rfl⟩ := hlmem y hy
    omega
  have hl : l.sum = 2 * (l.map (· / 2)).sum := by
    rw [← List.sum_map_mul_left]
    conv_lhs => rw [← List.map_id l]
    exact congrArg List.sum (List.map_congr_left fun y hy => (hhalf y hy).symm)
  have hmem : ∀ y ∈ l.map (· / 2), y ∈ eisTraces (k - lam) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨ψ, hψ, rfl⟩ := hlmem z hz
    rw [show 2 * T ψ / 2 = T ψ by omega]
    exact mem_eisTraces (hD.charSumEis_norm hφ h3 (Finset.ne_of_mem_erase hψ))
  have h1 := mem_reachMod (N := N) (A := eisTraces (k - lam)) (l.map (· / 2))
    [(∑ x, (D x : ℤ)) % N] (∑ x, (D x : ℤ)) hmem (List.mem_singleton_self _)
  have hlen : (l.map (· / 2)).length = (N - 1) / 2 := by
    rw [List.length_map]
    omega
  have hsum : ∑ x, (D x : ℤ) + (l.map (· / 2)).sum = N * contract φ D 0 := by
    linarith
  rw [hlen, hsum, Int.mul_emod_right] at h1
  exact hkill _ hs' h1

end SignedDifferenceSets
