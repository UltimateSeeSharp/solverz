module

public import CatchUp.BoCowgill.LowerRayInteriorReduction
public import CatchUp.Small

/-!
# The lower ray gives the conjecture

C74 for every `N`: C1 follows from three open families on the lower ray, for every `N ≥ 13` with
an even total: C82's start draws, C74's interior cases are no loss (C81 at `j = 2`) and its
boundary cases are no loss (C83). Up to `N = 12`, `conjecture_le_twelve`; there the hypotheses
are not needed, and at `N = 7, 8` they fail (C74's boundary). C92 for every `N` likewise: C82's
start, `({5..N}, 4)` and `{3..N}` minus one adjacent pair at deficit `2` drawing.
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
    Goal := by
  intro N hN
  by_cases h13 : 13 ≤ N
  · exact value_Icc_eq_draw_of_lower_ray_interior_and_boundary N (by omega) (hstart N h13 hN)
      (hinterior N h13 hN) (hboundary N h13 hN)
  · exact conjecture_le_twelve N (by omega) hN

/-- **The canonical ray's reduction** (C92 for every `N`): three draw families for `N ≥ 13`. -/
theorem conjecture_of_canonical_ray
    (hstart : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) →
      (pairDeletionPosition N 1 2).value = .draw)
    (hfour : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) →
      (lowerRayExactDeficitOpeningFourPosition N).value = .draw)
    (htwo : ∀ N, 13 ≤ N → Even (N * (N + 1) / 2) → ∀ b, 4 ≤ b → b ≤ N →
      (lowerRayExactDeficitOpeningTwoPosition N b).value = .draw) :
    Goal := by
  intro N hN
  by_cases h13 : 13 ≤ N
  · exact value_Icc_eq_draw_of_exact_deficit_canonical_openings N (by omega) (hstart N h13 hN)
      (hfour N h13 hN) (htwo N h13 hN)
  · exact conjecture_le_twelve N (by omega) hN

end CatchUp
