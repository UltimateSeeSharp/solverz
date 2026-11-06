module

public import SignedDifferenceSets.SetCheck

/-!
# N131: a (32, 20, 4) SDS in C₂ × C₁₆

Open in Gordon's table (`SDS(32,20,4,[2,16])`, 2026-11-05). The set is object O13
(`objects/O13.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N131

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O13's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xa73741d1

set_option linter.style.longLine false in
/-- Object O13's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x10809000

/-- Object O13: the sign of each element. -/
def sds : ZMod 2 × ZMod 16 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 20 4 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 16) (P := plus) (N := minus) (by decide +kernel)

/-- N131: C₂ × C₁₆ has a signed difference set with parameters (32, 20, 4). -/
theorem hasSDS : HasSDS (ZMod 2 × ZMod 16) 20 4 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N131
