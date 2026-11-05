module

public import SignedDifferenceSets.Statement

/-!
# Symmetries of a signed difference set (F2)

Translating an SDS, x ↦ D(x + t), or negating it keeps it an SDS with the same parameters.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {D : G → SignType}

/-- F2: a translate of an SDS is an SDS with the same parameters. -/
theorem IsSDS.translate (h : IsSDS k lam D) (t : G) : IsSDS k lam (fun x => D (x + t)) := by
  obtain ⟨hcard, hsum⟩ := h
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hcard]
    exact Finset.card_bij (fun x _ => x + t) (by simp) (by simp)
      (fun y hy => ⟨y - t, by simpa using hy, by simp⟩)
  · rw [← hsum g hg]
    exact Fintype.sum_equiv (Equiv.addRight t) _ _ (fun x => by simp [add_right_comm])

/-- F2: the negation of an SDS is an SDS with the same parameters. -/
theorem IsSDS.neg (h : IsSDS k lam D) : IsSDS k lam (fun x => -D x) := by
  obtain ⟨hcard, hsum⟩ := h
  refine ⟨by simpa using hcard, fun g hg => ?_⟩
  rw [← hsum g hg]
  simp [SignType.coe_neg]

end SignedDifferenceSets
