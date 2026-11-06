module

public import SignedDifferenceSets.Check
public import SignedDifferenceSets.Symmetry

/-!
# N3: no (9, 8, 1) SDS in C₃ × C₃

Open in Gordon's table (`SDS(9,8,1,[3,3])`, 2026-11-05). One of the nine elements is
unmarked; translating it to `0` (C2) leaves 3⁸ sign patterns, which `decide` rules out.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N3

/-- The sign function with `0` unmarked and the given signs elsewhere. -/
def mk (a b c d e f g h : SignType) : ZMod 3 × ZMod 3 → SignType := fun p =>
  ![![0, a, b], ![c, d, e], ![f, g, h]] p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates every sign pattern (or vector) in the kernel.
theorem mk_not_sds : ∀ a b c d e f g h : SignType, ¬ IsSDS 8 1 (mk a b c d e f g h) := by
  decide

theorem eq_mk (D : ZMod 3 × ZMod 3 → SignType) (h0 : D 0 = 0) :
    D = mk (D (0, 1)) (D (0, 2)) (D (1, 0)) (D (1, 1)) (D (1, 2)) (D (2, 0)) (D (2, 1))
      (D (2, 2)) := by
  funext p
  obtain ⟨x, y⟩ := p
  fin_cases x <;> fin_cases y <;> first | exact h0 | rfl

/-- N3: C₃ × C₃ has no signed difference set with parameters (9, 8, 1). -/
theorem not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 3) 8 1 := by
  rintro ⟨D, hD⟩
  obtain ⟨z, hz⟩ : ∃ z, D z = 0 := by
    by_contra hne
    have hall : ∀ x, D x ≠ 0 := fun x hx => hne ⟨x, hx⟩
    have hcard := hD.1
    rw [Finset.filter_true_of_mem (fun x _ => hall x)] at hcard
    simp at hcard
  have hT := hD.translate z
  rw [eq_mk (fun x => D (x + z)) (by simpa using hz)] at hT
  exact mk_not_sds _ _ _ _ _ _ _ _ hT

end SignedDifferenceSets.Answer.N3
