module

public import SignedDifferenceSets.SetCheck

/-!
# N169: a (36, 11, 2) SDS in C₃ × C₁₂

Open in Gordon's table (`SDS(36,11,2,[3,12])`, 2026-11-05). The set is object O21
(`objects/O21.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N169

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O21's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xcd4180801

set_option linter.style.longLine false in
/-- Object O21's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x8000000

/-- Object O21: the sign of each element. -/
def sds : ZMod 3 × ZMod 12 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 11 2 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 12) (P := plus) (N := minus) (by decide +kernel)

/-- N169: C₃ × C₁₂ has a signed difference set with parameters (36, 11, 2). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 12) 11 2 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N169
