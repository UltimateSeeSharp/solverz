module

public import SignedDifferenceSets.EisensteinCharsRows

/-!
# Tests for C20's checker

N1605, killed by C20, as its concrete statement. On N19 and N73, where a set exists, the checker
rejects every quotient C₃ᵃ, as it must.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- N1605: no (90, 85, 4) SDS in C₃ × C₃₀ (quotient C₃ × C₃, `s = 21`). -/
example : ¬ HasSDS (ZMod 3 × ZMod 30) 85 4 :=
  EcCert.not_hasSDS (r := ⟨1605, [3, 30], 85, 4⟩) (c := ⟨[3, 3], 21⟩) (by decide +kernel) _

-- N19 exists (C₃ × C₆, `s = 9`): no quotient C₃ᵃ kills it.
example : ¬ EcCert.Kills ⟨19, [3, 6], 13, 4⟩ ⟨[3, 1], 9⟩ := by decide +kernel
example : ¬ EcCert.Kills ⟨19, [3, 6], 13, 4⟩ ⟨[3, 3], 9⟩ := by decide +kernel

-- N73 exists (C₃³, `s = 15`): no quotient C₃ᵃ kills it.
example : ¬ EcCert.Kills ⟨73, [3, 3, 3], 17, 8⟩ ⟨[3, 1, 1], 15⟩ := by decide +kernel
example : ¬ EcCert.Kills ⟨73, [3, 3, 3], 17, 8⟩ ⟨[3, 3, 1], 15⟩ := by decide +kernel
example : ¬ EcCert.Kills ⟨73, [3, 3, 3], 17, 8⟩ ⟨[3, 3, 3], 15⟩ := by decide +kernel

end SignedDifferenceSets.Tests
