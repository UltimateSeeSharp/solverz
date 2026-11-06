module

public import SignedDifferenceSets.SetCheck

/-!
# N678: a (64, 22, 6) SDS in C₈ × C₈

Open in Gordon's table (`SDS(64,22,6,[8,8])`, 2026-11-05). The set is object O27
(`objects/O27.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N678

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O27's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x81412111090503fe

set_option linter.style.longLine false in
/-- Object O27's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O27: the sign of each element. -/
def sds : ZMod 8 × ZMod 8 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 22 6 sds :=
  isSDS_of_checkSet (G := ZMod 8 × ZMod 8) (P := plus) (N := minus) (by decide +kernel)

/-- N678: C₈ × C₈ has a signed difference set with parameters (64, 22, 6). -/
theorem hasSDS : HasSDS (ZMod 8 × ZMod 8) 22 6 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N678
