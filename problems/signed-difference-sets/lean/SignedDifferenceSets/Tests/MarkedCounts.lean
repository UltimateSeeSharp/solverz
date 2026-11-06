module

public import SignedDifferenceSets.MarkedCountsCheck

/-!
# Tests for C7's checker

N340, killed by C7, as its concrete statement. On N19 and N1640, where a set exists, C5's data
is valid but the checker rejects the LP's best weights, as it must.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- N340: no (48, 42, 6) SDS in C₂ × C₂ × C₁₂ (quotient C₂ × C₂ × C₄, `p = 3`, upper weights). -/
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 12) 42 6 :=
  McCert.not_hasSDS (r := ⟨340, [2, 2, 12], 42, 6⟩)
    (c := ⟨⟨3, 1, 1, [2, 2, 4], 18⟩, [⟨1, 0, 18, 9⟩]⟩) (by decide +kernel) _

-- N19 exists (C₃ × C₆ → C₂, `p = 3`): valid data, but no weights kill it.
example : (⟨3, 1, 1, [1, 2], 9⟩ : ScCert).Valid ⟨19, [3, 6], 13, 4⟩ := by
  unfold ScCert.Valid; decide +kernel
example : ¬ McCert.Kills ⟨19, [3, 6], 13, 4⟩
    ⟨⟨3, 1, 1, [1, 2], 9⟩, [⟨0, 1, 0, 1⟩, ⟨1, -12, 108, 9⟩, ⟨0, -1, 0, 1⟩, ⟨1, 12, 108, 9⟩]⟩ := by
  decide +kernel

-- N1640 exists (C₉₁ → C₁₃, `p = 2`, `q = 4`): the LP gives 74 ≤ k = 76 ≤ 78.
example : (⟨2, 2, 6, [13], 74⟩ : ScCert).Valid ⟨1640, [91], 76, 60⟩ := by
  unfold ScCert.Valid; decide +kernel
example : ¬ McCert.Kills ⟨1640, [91], 76, 60⟩
    ⟨⟨2, 2, 6, [13], 74⟩, [⟨1, 0, 12, 8⟩, ⟨0, 0, 6, 1⟩]⟩ := by
  decide +kernel

end SignedDifferenceSets.Tests
