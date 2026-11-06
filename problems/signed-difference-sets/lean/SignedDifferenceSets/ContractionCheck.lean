module

public import SignedDifferenceSets.Contraction
public import SignedDifferenceSets.Index
public import SignedDifferenceSets.VectorSearch

/-!
# Non-existence by contraction, checked by the kernel

`not_hasSDS_of_noVector`: if `noVector` finds no integer vector on `H` meeting what C3
demands of the coset sums along a surjection `G → H` with fibres of size `c`, then `G`
has no SDS (v, k, λ). A `Proj` builds the surjection factor by factor
(`ZMod m → ZMod d` for `d ∣ m`, identities, products).
-/

@[expose] public section

namespace SignedDifferenceSets

/-- A surjective homomorphism, built factor by factor. -/
structure Proj (G H : Type*) [AddCommGroup G] [AddCommGroup H] where
  hom : G →+ H
  surj : Function.Surjective hom

namespace Proj

/-- Reduction `ZMod m → ZMod d` for `d ∣ m` (`d = m`: the identity). -/
def cast {m : ℕ} (d : ℕ) (h : d ∣ m) : Proj (ZMod m) (ZMod d) :=
  ⟨(ZMod.castHom h (ZMod d)).toAddMonoidHom, ZMod.ringHom_surjective _⟩

/-- Factorwise on a product. -/
def prod {G H G' H' : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup G']
    [AddCommGroup H'] (p : Proj G H) (q : Proj G' H') : Proj (G × G') (H × H') :=
  ⟨p.hom.prodMap q.hom, by rw [AddMonoidHom.coe_prodMap]; exact p.surj.prodMap q.surj⟩

end Proj

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- The square of the sum is the sum of the autocorrelations at every shift. -/
theorem sum_mul_sum_eq (a : H → ℤ) : (∑ h, a h) * ∑ h, a h = ∑ g, ∑ h, a h * a (h + g) := by
  rw [Finset.sum_mul_sum]
  calc ∑ i, ∑ j, a i * a j = ∑ i, ∑ g, a i * a (i + g) :=
        Finset.sum_congr rfl fun i _ =>
          (Fintype.sum_equiv (Equiv.addLeft i) _ (fun j => a i * a j) fun _ => rfl).symm
    _ = _ := Finset.sum_comm

/-- What contraction with fibres of size `c` demands of the coset sums `b` (C3, and the
absolute sum and parity of `IsSDS.sum_abs_contract_le`, `IsSDS.sum_abs_contract_parity`). -/
structure Demands (c k : ℕ) (lam : ℤ) (b : H → ℤ) : Prop where
  bound : ∀ h, |b h| ≤ c
  sq : ∑ h, b h * b h = k + lam * ((c : ℤ) - 1)
  corr : ∀ g, g ≠ 0 → ∑ h, b h * b (h + g) = lam * c
  abs : ∑ h, |b h| ≤ k
  parity : ((k : ℤ) - ∑ h, |b h|) % 2 = 0

variable {c k : ℕ} {lam : ℤ} {b : H → ℤ}

theorem Demands.neg (hb : Demands c k lam b) : Demands c k lam (fun h => -b h) where
  bound h := by rw [abs_neg]; exact hb.bound h
  sq := by simpa only [neg_mul_neg] using hb.sq
  corr g hg := by simpa only [neg_mul_neg] using hb.corr g hg
  abs := by simpa only [abs_neg] using hb.abs
  parity := by simpa only [abs_neg] using hb.parity

theorem Demands.translate (hb : Demands c k lam b) (h₀ : H) :
    Demands c k lam (fun h => b (h + h₀)) where
  bound h := hb.bound _
  sq := by rw [← hb.sq]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun _ => rfl
  corr g hg := by
    rw [← hb.corr g hg]
    simp only [add_right_comm _ g h₀]
    exact Fintype.sum_equiv (Equiv.addRight h₀) _ (fun u => b u * b (u + g)) fun _ => rfl
  abs := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.abs
  parity := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.parity

variable [Indexed H]

theorem getD_ofFn {n : ℕ} (F : Fin n → ℤ) {i : ℕ} (hi : i < n) :
    (List.ofFn F).getD i 0 = F ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- A vector meeting the demands, `Σ b = s` and `|b 0|` largest, contradicts `noVector`. -/
theorem false_of_noVector {s : ℤ}
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c (k + lam * ((c : ℤ) - 1)) (lam * c) k s
      = true)
    (hb : Demands c k lam b) (hmax : ∀ h, |b h| ≤ |b 0|) (hs : ∑ h, b h = s) : False := by
  set n := Indexed.size H
  set e : H ≃ Fin n := Indexed.equiv
  have hpos : 0 < n := (e 0).pos
  have he0 : e.symm ⟨0, hpos⟩ = 0 := e.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  set F : Fin n → ℤ := fun i => b (e.symm i)
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have hne : List.ofFn F ≠ [] := by
    intro h
    have := List.length_ofFn (f := F)
    rw [h] at this
    simp at this
    omega
  obtain ⟨x, w, hL⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = b 0 := by
    have := getD_ofFn F hpos
    rw [hL] at this
    simpa [F, he0] using this
  have hw : ∀ y ∈ w, ∃ h, b h = y := fun y hy => hmem y (hL ▸ List.mem_cons_of_mem x hy)
  refine noVector_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
    (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hx ▸ hmax h
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hb.bound h
  · rw [← hL, ← hs]
    simpa using hsum id
  · rw [← hL, ← hb.sq]
    exact hsum fun y => y * y
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.abs
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.parity
  · rw [← hL, shiftsOK, allTo_iff]
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp
    set gH := e.symm ⟨g, hg⟩
    have hgH : (e gH : ℕ) = g := by simp [gH]
    have hgH0 : gH ≠ 0 := by
      intro h0
      have := hgH
      rw [h0, Indexed.equiv_zero] at this
      omega
    simp only [Bool.or_eq_true, beq_iff_eq]
    right
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := H)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- No SDS (v, k, λ) on `G` when `noVector` rules out the coset sums along `p`, whose
fibres have `c = |G| / |H|` elements; `s² = k + λ(v − 1)` (C1). -/
theorem not_hasSDS_of_noVector (p : Proj G H) (c : ℕ) (s : ℤ)
    (hc : Fintype.card G = c * Fintype.card H)
    (hs : s * s = k + lam * ((Fintype.card G : ℤ) - 1))
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c (k + lam * ((c : ℤ) - 1)) (lam * c) k s
      = true) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  have hfib := card_fibre_eq p.surj hc
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hc, h0, zero_mul] at this
      omega
    · exact h0
  set a := contract p.hom D
  have hdem : Demands c k lam a :=
    { bound := fun h => by
        have := abs_contract_le p.hom D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq p.hom, hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr p.hom g hg, hfib]
      abs := hD.sum_abs_contract_le p.hom
      parity := hD.sum_abs_contract_parity p.hom }
  have hH1 : 1 ≤ Fintype.card H := Fintype.card_pos
  have hsq : (∑ h, a h) * (∑ h, a h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hdem.sq, Finset.sum_congr rfl fun g hg => hdem.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hs, hc,
      nsmul_eq_mul, Nat.cast_sub hH1]
    push_cast
    ring
  -- `Σ a = ±s`: negate if needed, then translate the largest entry to `0`.
  have key : ∀ b : H → ℤ, Demands c k lam b → ∑ h, b h = s → False := by
    intro b hb hbs
    obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b h|)
      Finset.univ_nonempty
    refine false_of_noVector hn (hb.translate h₀) (fun h => ?_) ?_
    · simpa using hmax (h + h₀) (Finset.mem_univ _)
    · rw [← hbs]
      exact Fintype.sum_equiv (Equiv.addRight h₀) _ b fun _ => rfl
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key a hdem h1
  · exact key _ hdem.neg (by rw [Finset.sum_neg_distrib, h1, neg_neg])

end SignedDifferenceSets
