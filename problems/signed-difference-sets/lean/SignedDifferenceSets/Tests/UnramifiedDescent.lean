module

public import SignedDifferenceSets.UnramifiedDescent

/-!
# Tests for C27

The rule kills N637 (63, 45, 2) in `C₆₃` (`n = 43`, multipliers `1, 22, 43 ≡ 1 mod 21`); it does
not fire on N3408 (126, 96, 32) or N6 (11, 6, 1), which have sets.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- N637: `m = 63`, `F = 21`, `c = 1`: `63 · 21 < φ(63) · 43 = 36 · 43`. -/
example : ¬ HasSDS (ZMod 63) 45 2 :=
  DescentRowCert.not_hasSDS (w := ⟨637, [63], 45, 2⟩) (c := ⟨63, 21, [1], [1]⟩)
    (by decide +kernel) _

/-- N3408 exists: on `C₉` (`F = 3`, `c = 14`) the bound holds, `9 · 3 · 14² ≥ φ(9) · 64`. -/
example : ¬ DescentRowCert.Kills ⟨3408, [126], 96, 32⟩ ⟨9, 3, [1], [1]⟩ := by decide +kernel

/-- N6 exists: on `C₁₁` only `F = 11` works, and `11 · 11 ≥ φ(11) · 5`. -/
example : ¬ DescentRowCert.Kills ⟨6, [11], 6, 1⟩ ⟨11, 11, [1], [1]⟩ := by decide +kernel

end SignedDifferenceSets
