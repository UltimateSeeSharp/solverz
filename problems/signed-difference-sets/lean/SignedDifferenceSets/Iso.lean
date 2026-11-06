module

public import SignedDifferenceSets.Statement

/-!
# `HasSDS` up to isomorphism

An SDS carried along a group isomorphism is an SDS with the same parameters, so `HasSDS`
depends on the group only up to `≃+`; nor does it depend on the `Fintype` instance.
-/

@[expose] public section

namespace SignedDifferenceSets

section Iso

variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  {k : ℕ} {lam : ℤ}

/-- An SDS pulled back along an isomorphism is an SDS. -/
theorem IsSDS.comp_addEquiv {D : G → SignType} (hD : IsSDS k lam D) (e : G' ≃+ G) :
    IsSDS k lam (D ∘ e) := by
  obtain ⟨hcard, hsum⟩ := hD
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hcard]
    exact Finset.card_bij (fun x _ => e x) (by simp) (by simp)
      (fun y hy => ⟨e.symm y, by simpa using hy, by simp⟩)
  · rw [← hsum (e g) (by simpa using hg)]
    exact Fintype.sum_equiv e.toEquiv _ _ (fun x => by simp [map_add])

/-- `HasSDS` transfers along an isomorphism. -/
theorem HasSDS.of_addEquiv (e : G ≃+ G') (h : HasSDS G k lam) : HasSDS G' k lam :=
  let ⟨D, hD⟩ := h
  ⟨D ∘ e.symm, hD.comp_addEquiv e.symm⟩

/-- Isomorphic groups have the same SDSs' parameters. -/
theorem hasSDS_congr (e : G ≃+ G') : HasSDS G k lam ↔ HasSDS G' k lam :=
  ⟨HasSDS.of_addEquiv e, HasSDS.of_addEquiv e.symm⟩

end Iso

/-- `HasSDS` does not depend on the `Fintype` instance. -/
theorem hasSDS_congr_fintype {G : Type*} [AddCommGroup G] (i₁ i₂ : Fintype G) (k : ℕ)
    (lam : ℤ) : @HasSDS G _ i₁ k lam ↔ @HasSDS G _ i₂ k lam := by
  rw [Subsingleton.elim i₁ i₂]

end SignedDifferenceSets
