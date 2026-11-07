import SignedDifferenceSets.SelfConjugacy

/-! Refuter: elaborated statement, axioms, and applicability to real rows (non-vacuity). -/

open SignedDifferenceSets

set_option pp.funBinderTypes true in
#check @not_hasSDS_of_selfConj
#print axioms not_hasSDS_of_selfConj
#print axioms IsSDS.contract_congr_pow

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Self-conjugacy from `dᵢ ∣ p^i + 1`, the certificates' form (no `decide` on `nsmul`). -/
theorem hc_of_dvd {a b N : ℕ} (ha : a ∣ N + 1) (hb : b ∣ N + 1) (x : ZMod a × ZMod b) :
    N • x = -x := by
  have h1 : ∀ {d : ℕ}, d ∣ N + 1 → ∀ y : ZMod d, (N + 1) • y = 0 := fun hd y => by
    rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff (ZMod _) _ _).2 hd, zero_mul]
  have h : (N + 1) • x = 0 := Prod.ext (h1 ha x.1) (h1 hb x.2)
  rw [add_nsmul, one_nsmul] at h
  exact eq_neg_of_add_eq_zero_left h

-- N30 SDS(20,11,2,[2,10]) cert: p=3 j=1 i=2 H=[2,10] (c = 1)
example : ¬ HasSDS (ZMod 2 × ZMod 10) 11 2 :=
  not_hasSDS_of_selfConj (AddMonoidHom.id _) Function.surjective_id (c := 1) (by simp)
    (p := 3) (i := 2) (j := 1) (by norm_num) (by decide) (by decide) ⟨(1, 0), by decide⟩
    (by norm_num) (by norm_num) (by norm_num)

-- N99 SDS(28,27,2,[2,14]) cert: p=5 j=1 i=3 H=[1,14] (c = 2, ZMod 1 factor)
example : ¬ HasSDS (ZMod 2 × ZMod 14) 27 2 :=
  not_hasSDS_of_selfConj
    (AddMonoidHom.prodMap (ZMod.castHom (by norm_num : 1 ∣ 2) (ZMod 1)).toAddMonoidHom
      (AddMonoidHom.id (ZMod 14)))
    (by rintro ⟨a, b⟩; exact ⟨(0, b), Prod.ext (Subsingleton.elim _ _) rfl⟩)
    (c := 2) (by rw [Fintype.card_prod, Fintype.card_prod]; norm_num [ZMod.card])
    (p := 5) (i := 3) (j := 1) (by norm_num) (hc_of_dvd (by norm_num) (by norm_num))
    (by rw [Fintype.card_prod, ZMod.card, ZMod.card]; decide) ⟨(0, 1), by decide⟩
    (by norm_num) (by norm_num) (by norm_num)

-- N1056 SDS(75,67,3,[5,15]) cert: p=2 j=3 i=2 H=[5,5] (c = 3)
example : ¬ HasSDS (ZMod 5 × ZMod 15) 67 3 :=
  not_hasSDS_of_selfConj
    (AddMonoidHom.prodMap (AddMonoidHom.id (ZMod 5))
      (ZMod.castHom (by norm_num : 5 ∣ 15) (ZMod 5)).toAddMonoidHom)
    (by
      rintro ⟨a, b⟩
      obtain ⟨b', hb'⟩ := ZMod.ringHom_surjective (ZMod.castHom (by norm_num : 5 ∣ 15) (ZMod 5)) b
      exact ⟨(a, b'), Prod.ext rfl hb'⟩)
    (c := 3) (by rw [Fintype.card_prod, Fintype.card_prod]; norm_num [ZMod.card])
    (p := 2) (i := 2) (j := 3) (by norm_num) (hc_of_dvd (by norm_num) (by norm_num))
    (by rw [Fintype.card_prod, ZMod.card]; decide) ⟨(1, 0), by decide⟩
    (by norm_num) (by norm_num) (by norm_num)
