module

public import SignedDifferenceSets.RealChars

/-!
# Gaussian characters on a quotient of exponent 4 (C19)

On a quotient `H` with `4h = 0` every character takes values in `{±1, ±i}`, so
`ψ(D) = A + B i` with integers `A`, `B` and `A² + B² = k − λ` for `ψ ≠ 1`. Real characters give
`±m` (`m² = k − λ`); the others pair with `−ψ`, which has the same `A`. Summing the real parts,
`|H| a₀ = s' + Σ ±m + 2 Σ x` with `x² + y² = k − λ`. A row dies when for every possible count of
real characters `0` is not reachable mod `|H|` (`GaussKills`).
-/

@[expose] public section

open ComplexConjugate

namespace SignedDifferenceSets

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] {k : ℕ} {lam : ℤ}
  {D : G → SignType}

/-! ### The norm identity -/

/-- C19 (a): every nontrivial character has `ψ(D) · conj ψ(D) = k − λ`. -/
theorem IsSDS.charSum_mul_conj [Finite H] (hD : IsSDS k lam D) {φ : G →+ H}
    (hφ : Function.Surjective φ) {ψ : AddChar H ℂ} (hψ : ψ ≠ 0) :
    charSum φ D ψ * conj (charSum φ D ψ) = (k : ℂ) - lam := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hsum : ∑ g, ψ (φ (-g)) = 0 := by
    have hne : ψ.compAddMonoidHom φ ≠ 0 := by
      intro h0
      refine hψ (AddChar.ext _ _ fun h => ?_)
      obtain ⟨g, rfl⟩ := hφ h
      simpa using DFunLike.congr_fun h0 g
    have h1 := AddChar.sum_eq_zero_iff_ne_zero.2 hne
    rw [← Equiv.sum_comp (Equiv.neg G)] at h1
    simpa using h1
  have hA (g : G) : ∑ x, ((D x : ℤ) : ℂ) * ((D (x + g) : ℤ) : ℂ) =
      lam + if g = 0 then (k : ℂ) - lam else 0 := by
    split_ifs with hg
    · subst hg
      have hk : ∑ x, (D x : ℤ) * (D (x + 0) : ℤ) = k := by
        simp only [add_zero]
        rw [← hD.1, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        cases D x <;> simp
      rw [show (lam : ℂ) + ((k : ℂ) - lam) = k by ring]
      exact_mod_cast hk
    · rw [add_zero]
      exact_mod_cast hD.2 g hg
  have hconj : conj (charSum φ D ψ) = ∑ y, ((D y : ℤ) : ℂ) * ψ (φ (-y)) := by
    simp only [charSum, map_sum, map_mul, map_intCast, map_neg,
      AddChar.map_neg_eq_conj]
  calc charSum φ D ψ * conj (charSum φ D ψ)
      = ∑ x, ∑ y, ((D x : ℤ) : ℂ) * ψ (φ x) * (((D y : ℤ) : ℂ) * ψ (φ (-y))) := by
        rw [hconj, charSum, Finset.sum_mul_sum]
    _ = ∑ x, ∑ g, ((D x : ℤ) : ℂ) * ψ (φ x) *
          (((D (x + g) : ℤ) : ℂ) * ψ (φ (-(x + g)))) :=
        Finset.sum_congr rfl fun x _ => (Equiv.sum_comp (Equiv.addLeft x) _).symm
    _ = ∑ g, ψ (φ (-g)) * ∑ x, ((D x : ℤ) : ℂ) * ((D (x + g) : ℤ) : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have : ψ (φ x) * ψ (φ (-(x + g))) = ψ (φ (-g)) := by
          rw [← AddChar.map_add_eq_mul, ← map_add]
          congr 2
          abel
        rw [← this]
        ring
    _ = (k : ℂ) - lam := by
        simp only [hA, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul,
          mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, neg_zero,
          map_zero, AddChar.map_zero_eq_one, one_mul, zero_add]

/-! ### Values on a group of exponent 4 -/

theorem pow_four_cases {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  have h : (z - 1) * (z + 1) * ((z - Complex.I) * (z + Complex.I)) = 0 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination hz - (z ^ 2 - 1) * hI
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
    · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

open scoped Classical in
/-- The real part of `ψ h ∈ {±1, ±i}` as an integer. -/
noncomputable def charRe (ψ : AddChar H ℂ) (h : H) : ℤ :=
  if ψ h = 1 then 1 else if ψ h = -1 then -1 else 0

open scoped Classical in
/-- The imaginary part of `ψ h ∈ {±1, ±i}` as an integer. -/
noncomputable def charIm (ψ : AddChar H ℂ) (h : H) : ℤ :=
  if ψ h = Complex.I then 1 else if ψ h = -Complex.I then -1 else 0

theorem charRe_add_charIm (h4 : ∀ h : H, 4 • h = 0) (ψ : AddChar H ℂ) (h : H) :
    (charRe ψ h : ℂ) + charIm ψ h * Complex.I = ψ h := by
  have h1 : ψ h ^ 4 = 1 := by rw [← AddChar.map_nsmul_eq_pow, h4, AddChar.map_zero_eq_one]
  have hI : Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h11 : (-1 : ℂ) ≠ 1 := by norm_num
  have hnI : -Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hI' : Complex.I ≠ -1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hnI' : -Complex.I ≠ -1 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hII : -Complex.I ≠ Complex.I := by
    intro h; have := congrArg Complex.im h; simp at this; norm_num at this
  rcases pow_four_cases h1 with e | e | e | e <;>
    simp [charRe, charIm, e, hI, hnI, hI', hnI', hII, hI.symm, hnI.symm, hI'.symm, hnI'.symm,
      h11]

/-- `Re ψ(D)` as an integer. -/
noncomputable def charSumRe (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  ∑ x, (D x : ℤ) * charRe ψ (φ x)

/-- `Im ψ(D)` as an integer. -/
noncomputable def charSumIm (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  ∑ x, (D x : ℤ) * charIm ψ (φ x)

theorem charSum_eq_re_im (h4 : ∀ h : H, 4 • h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) :
    charSum φ D ψ = (charSumRe φ D ψ : ℂ) + charSumIm φ D ψ * Complex.I := by
  simp only [charSum, charSumRe, charSumIm, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← charRe_add_charIm h4 ψ (φ x)]
  ring

/-- `(−ψ)(D) = conj ψ(D)`. -/
theorem charSum_neg [Finite H] (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) :
    charSum φ D (-ψ) = conj (charSum φ D ψ) := by
  simp only [charSum, map_sum, map_mul, map_intCast, AddChar.neg_apply,
    AddChar.map_neg_eq_conj]

theorem charSumRe_neg [Finite H] (h4 : ∀ h : H, 4 • h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) :
    charSumRe φ D (-ψ) = charSumRe φ D ψ ∧ charSumIm φ D (-ψ) = -charSumIm φ D ψ := by
  have h := charSum_neg φ D ψ
  rw [charSum_eq_re_im h4, charSum_eq_re_im h4] at h
  have h1 : ((charSumRe φ D (-ψ) : ℤ) : ℝ) = charSumRe φ D ψ := by
    simpa using congrArg Complex.re h
  have h2 : ((charSumIm φ D (-ψ) : ℤ) : ℝ) = -charSumIm φ D ψ := by
    simpa using congrArg Complex.im h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- C19 (a'): on a group of exponent 4, `Re² + Im² = k − λ` for a nontrivial character. -/
theorem IsSDS.charSumRe_sq_add [Finite H] (hD : IsSDS k lam D) {φ : G →+ H}
    (hφ : Function.Surjective φ) (h4 : ∀ h : H, 4 • h = 0) {ψ : AddChar H ℂ} (hψ : ψ ≠ 0) :
    charSumRe φ D ψ ^ 2 + charSumIm φ D ψ ^ 2 = k - lam := by
  have h := hD.charSum_mul_conj hφ hψ
  rw [charSum_eq_re_im h4] at h
  suffices hh : ((charSumRe φ D ψ : ℝ)) ^ 2 + (charSumIm φ D ψ : ℝ) ^ 2 = (k : ℝ) - lam by
    exact_mod_cast hh
  simpa [Complex.mul_re, sq] using congrArg Complex.re h

/-- C19 (b): the real parts add up to `|H| · a₀`. -/
theorem sum_charSumRe [Fintype H] [DecidableEq H] (h4 : ∀ h : H, 4 • h = 0) (φ : G →+ H)
    (D : G → SignType) :
    ∑ ψ : AddChar H ℂ, charSumRe φ D ψ = Fintype.card H * contract φ D 0 := by
  have h := sum_charSum φ D
  simp only [charSum_eq_re_im h4] at h
  have h1 : ((∑ ψ : AddChar H ℂ, charSumRe φ D ψ : ℤ) : ℝ) =
      ((Fintype.card H * contract φ D 0 : ℤ) : ℝ) := by
    push_cast
    simpa using congrArg Complex.re h
  exact_mod_cast h1

/-! ### Pairing and residues -/

/-- A finset closed under a fixed-point-free negation splits into pairs `{a, −a}`. -/
theorem exists_pair_list {α : Type*} [InvolutiveNeg α] (f : α → ℤ)
    (hf : ∀ a, f (-a) = f a) (T : Finset α) (hc : ∀ a ∈ T, -a ∈ T) (hne : ∀ a ∈ T, -a ≠ a) :
    ∃ l : List ℤ, 2 * l.length = T.card ∧ (∀ y ∈ l, ∃ a ∈ T, y = 2 * f a) ∧
      l.sum = ∑ a ∈ T, f a := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨[], by simp, by simp, by simp⟩
    · have hna : -a ∈ T.erase a := Finset.mem_erase.2 ⟨hne a ha, hc a ha⟩
      set T' := (T.erase a).erase (-a) with hT'
      have hsub : T' ⊂ T :=
        (Finset.erase_ssubset hna).trans_le (Finset.erase_subset _ _)
      have hmem (b : α) : b ∈ T' ↔ b ∈ T ∧ b ≠ a ∧ b ≠ -a := by
        simp only [hT', Finset.mem_erase]; tauto
      obtain ⟨l, hl1, hl2, hl3⟩ := ih T' hsub
        (fun b hb => by
          obtain ⟨hbT, hba, hbna⟩ := (hmem b).1 hb
          refine (hmem _).2 ⟨hc b hbT, fun h => hbna ?_, fun h => hba ?_⟩
          · rw [← h, neg_neg]
          · exact neg_injective h)
        (fun b hb => hne b ((hmem b).1 hb).1)
      have hc1 : T'.card + 2 = T.card := by
        rw [hT', Finset.card_erase_of_mem hna, Finset.card_erase_of_mem ha]
        have h1 : 0 < (T.erase a).card := Finset.card_pos.2 ⟨-a, hna⟩
        have h2 : 0 < T.card := Finset.card_pos.2 ⟨a, ha⟩
        rw [Finset.card_erase_of_mem ha] at h1
        omega
      refine ⟨2 * f a :: l, ?_, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, ha, rfl⟩
        · obtain ⟨b, hb, rfl⟩ := hl2 y hy
          exact ⟨b, ((hmem b).1 hb).1, rfl⟩
      · rw [List.sum_cons, hl3, ← Finset.add_sum_erase _ _ ha,
          ← Finset.add_sum_erase _ _ hna, hf]
        ring

/-- Residues mod `N` reachable from `S` by adding `a` values from `A`. -/
def reachMod (N : ℤ) (A : List ℤ) : ℕ → List ℤ → List ℤ
  | 0, S => S
  | a + 1, S => reachMod N A a ((S.flatMap fun r => A.map fun x => (r + x) % N).dedup)

theorem mem_reachMod {N : ℤ} {A : List ℤ} :
    ∀ (l S : List ℤ) (r : ℤ), (∀ x ∈ l, x ∈ A) → r % N ∈ S →
      (r + l.sum) % N ∈ reachMod N A l.length S
  | [], S, r, _, hr => by simpa [reachMod] using hr
  | x :: l, S, r, hl, hr => by
    simp only [List.length_cons, reachMod, List.sum_cons]
    have hmem : (r + x) % N ∈ (S.flatMap fun r => A.map fun x => (r + x) % N).dedup := by
      rw [List.mem_dedup, List.mem_flatMap]
      exact ⟨r % N, hr, List.mem_map.2 ⟨x, hl x List.mem_cons_self, Int.emod_add_emod r N x⟩⟩
    have h := mem_reachMod l _ (r + x) (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hmem
    rwa [add_assoc] at h

/-- The `x ∈ [−m, m]` with `x² + y² = n` for some `y ∈ [0, m]`. -/
def gaussX (n m : ℤ) : List ℤ :=
  ((List.range (2 * m.toNat + 1)).map fun i : ℕ => (i : ℤ) - m).filter fun x =>
    (List.range (m.toNat + 1)).any fun y => x ^ 2 + (y : ℤ) ^ 2 == n

theorem mem_gaussX {m a b : ℤ} (hm : 0 ≤ m) (h : a ^ 2 + b ^ 2 = m ^ 2) :
    a ∈ gaussX (m ^ 2) m := by
  have ha : |a| ≤ m := by
    rw [← abs_of_nonneg hm]; exact sq_le_sq.1 (by nlinarith [sq_nonneg b])
  have hb : |b| ≤ m := by
    rw [← abs_of_nonneg hm]; exact sq_le_sq.1 (by nlinarith [sq_nonneg a])
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have e1 := Int.toNat_of_nonneg (show 0 ≤ a + m by omega)
  have e2 := Int.toNat_of_nonneg hm
  have e3 := Int.toNat_of_nonneg (abs_nonneg b)
  have i1 : (a + m).toNat < 2 * m.toNat + 1 := by
    have : ((a + m).toNat : ℤ) < 2 * (m.toNat : ℤ) + 1 := by rw [e1, e2]; omega
    exact_mod_cast this
  have i2 : ((a + m).toNat : ℤ) - m = a := by rw [e1]; ring
  have i3 : |b|.toNat < m.toNat + 1 := by
    have : (|b|.toNat : ℤ) < (m.toNat : ℤ) + 1 := by rw [e3, e2]; omega
    exact_mod_cast this
  unfold gaussX
  rw [List.mem_filter, List.any_eq_true]
  refine ⟨List.mem_map.2 ⟨(a + m).toNat, List.mem_range.2 i1, i2⟩, |b|.toNat,
    List.mem_range.2 i3, ?_⟩
  rw [beq_iff_eq, e3, sq_abs, h]

/-- The kill condition of C19 for a quotient of order `N`, `m = √(k − λ)` and sign sum `±s`:
for every count `R` of real characters with `N − R` even, `0` is not reachable mod `N`. -/
def GaussKills (N : ℕ) (m s : ℤ) : Prop :=
  0 ≤ m ∧ ∀ s' ∈ [s, -s], ∀ R ∈ List.range (N + 1), 1 ≤ R → (N - R) % 2 = 0 →
    (0 : ℤ) ∉ reachMod N ((gaussX (m ^ 2) m).map (2 * ·)) ((N - R) / 2)
      (reachMod N [m, -m] (R - 1) [s' % N])

instance (N : ℕ) (m s : ℤ) : Decidable (GaussKills N m s) := by
  unfold GaussKills; infer_instance

/-- C19: no SDS when `k − λ = m²`, `s² = k + λ(v − 1)` and a quotient of exponent 4 passes
`GaussKills`. -/
theorem not_hasSDS_of_gaussChars [Fintype H] {φ : G →+ H}
    (hφ : Function.Surjective φ) (h4 : ∀ h : H, 4 • h = 0) {m s : ℤ} (hm : m ^ 2 = k - lam)
    (hs : s ^ 2 = k + lam * ((Fintype.card G : ℤ) - 1))
    (hkill : GaussKills (Fintype.card H) m s) : ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  obtain ⟨hm0, hk⟩ := hkill
  set N := Fintype.card H with hN
  have hs' : (∑ x, (D x : ℤ)) ∈ [s, -s] := by
    have h := hD.sum_sq
    rw [← hs] at h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h <;> simp [h]
  set A := charSumRe φ D
  have hA0 : A 0 = ∑ x, (D x : ℤ) := by simp [A, charSumRe, charRe]
  set Rl := Finset.univ.filter fun ψ : AddChar H ℂ => -ψ = ψ
  set NR := Finset.univ.filter fun ψ : AddChar H ℂ => ¬ -ψ = ψ
  have h0R : (0 : AddChar H ℂ) ∈ Rl := by simp [Rl]
  have hreal (ψ : AddChar H ℂ) (hψ : ψ ∈ Rl.erase 0) : A ψ ∈ [m, -m] := by
    have hne : ψ ≠ 0 := Finset.ne_of_mem_erase hψ
    have hneg : -ψ = ψ := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hψ)).2
    obtain ⟨-, h2⟩ := charSumRe_neg h4 φ D ψ
    rw [hneg] at h2
    have him : charSumIm φ D ψ = 0 := by linarith
    have hsq := hD.charSumRe_sq_add hφ h4 hne
    rw [him, ← hm] at hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (by simpa using hsq) with h | h <;> simp [A, h]
  obtain ⟨l2, hl2len, hl2mem, hl2sum⟩ := exists_pair_list A
    (fun ψ => (charSumRe_neg h4 φ D ψ).1) NR
    (fun ψ hψ => by
      simp only [NR, Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      rwa [neg_neg, eq_comm])
    (fun ψ hψ => (Finset.mem_filter.1 hψ).2)
  set l1 := (Rl.erase 0).toList.map A
  have hl1sum : l1.sum = ∑ ψ ∈ Rl.erase 0, A ψ := by
    simp [l1, Finset.sum_map_toList]
  have hl1len : l1.length = Rl.card - 1 := by
    simp [l1, Finset.card_erase_of_mem h0R]
  have hcard : Rl.card + NR.card = N := by
    simp only [Rl, NR]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, AddChar.card_eq]
  have htot : ∑ ψ, A ψ = (N : ℤ) * contract φ D 0 := sum_charSumRe h4 φ D
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ψ : AddChar H ℂ => -ψ = ψ),
    ← Finset.add_sum_erase _ _ h0R, hA0, ← hl1sum, ← hl2sum] at htot
  have hR1 : 1 ≤ Rl.card := Finset.card_pos.2 ⟨0, h0R⟩
  have hX : ∀ y ∈ l2, y ∈ (gaussX (m ^ 2) m).map (2 * ·) := by
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := hl2mem y hy
    have hne : ψ ≠ 0 := by
      intro h; subst h; exact (Finset.mem_filter.1 hψ).2 (by simp)
    have hsq := hD.charSumRe_sq_add hφ h4 hne
    rw [← hm] at hsq
    exact List.mem_map.2 ⟨A ψ, mem_gaussX hm0 hsq, rfl⟩
  have h1 := mem_reachMod (N := N) (A := [m, -m]) l1 [(∑ x, (D x : ℤ)) % N] (∑ x, (D x : ℤ))
    (fun x hx => by
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hx
      exact hreal ψ (Finset.mem_toList.1 hψ)) (List.mem_singleton_self _)
  have h2 := mem_reachMod (N := N) (A := (gaussX (m ^ 2) m).map (2 * ·)) l2 _ _ hX h1
  rw [hl1len] at h2
  have hlen2 : l2.length = (N - Rl.card) / 2 := by omega
  rw [hlen2, htot] at h2
  refine hk _ hs' Rl.card (List.mem_range.2 (by omega)) hR1 (by omega) ?_
  simpa using h2

end SignedDifferenceSets
