module

public import CatchUp.LowerRayInteriorReduction
public import CatchUp.Small

/-!
# The lower ray gives the conjecture

C74 for every `N`: C1 follows from three open families on the lower ray, for every `N ≥ 13` with
an even total: C82's start draws, C74's interior cases are no loss (C81 at `j = 2`) and its
boundary cases are no loss (C83). Up to `N = 12`, `conjecture_le_twelve`; there the hypotheses
are not needed, and at `N = 7, 8` they fail (C74's boundary).
-/

@[expose] public section

namespace CatchUp

/-- **The lower ray's reduction** (C74 for every `N`; C81 at `j = 2`, C82, C83 ⇒ C1). -/
theorem conjecture_of_lower_ray
    (hstart : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) →
      (pairDeletionPosition N 1 2).value = .draw)
    (hinterior : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) →
      ∀ b, 3 ≤ b → b ≤ N → LowerRayInteriorDeficitOneNonloss N b)
    (hboundary : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) → ∀ b, 3 ≤ b → b ≤ N →
      ∀ y ∈ lowerRayExactDeficitResidual N b, (y = 2 ∨ y = b - 2 ∨ y = b + 1 ∨ y = N) →
        (afterOpening (lowerRayExactDeficitResidual N b) y).value ≠ .loss) :
    Conjecture := by
  intro N hN
  by_cases h13 : 13 ≤ N
  · exact value_Icc_eq_draw_of_lower_ray_interior_and_boundary N (by omega) (hstart N h13 hN)
      (hinterior N h13 hN) (hboundary N h13 hN)
  · exact conjecture_le_twelve N (by omega) hN

end CatchUp
