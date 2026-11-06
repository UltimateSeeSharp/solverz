module

public import SignedDifferenceSets.SetCheck

/-!
# N31: a (20, 11, 2) SDS in C₂₀

Open in Gordon's table (`SDS(20,11,2,[20])`, 2026-11-05). The set is object O95
(`objects/O95.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N31

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O95's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x442cf

set_option linter.style.longLine false in
/-- Object O95's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x8020

/-- Object O95: the sign of each element. -/
def sds : ZMod 20 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 11 2 sds :=
  isSDS_of_checkSet (G := ZMod 20)
    (P := plus) (N := minus) (by decide +kernel)

/-- N31: C₂₀ has a signed difference set with
parameters (20, 11, 2). -/
theorem hasSDS :
    HasSDS (ZMod 20) 11 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N31
