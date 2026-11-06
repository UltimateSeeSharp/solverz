module

public import SignedDifferenceSets.SetCheck

/-!
# N11991: a (222, 69, 20) SDS in C₂₂₂

Open in Gordon's table (`SDS(222,69,20,[222])`, 2026-11-05). The set is object O37
(`objects/O37.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N11991

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O37's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xc0e0b1c036c001060129518aa068044124248118403117374104297

set_option linter.style.longLine false in
/-- Object O37's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4000000000000000000

/-- Object O37: the sign of each element. -/
def sds : ZMod 222 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 69 20 sds :=
  isSDS_of_checkSet (G := ZMod 222)
    (P := plus) (N := minus) (by decide +kernel)

/-- N11991: C₂₂₂ has a signed difference set with
parameters (222, 69, 20). -/
theorem hasSDS :
    HasSDS (ZMod 222) 69 20 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N11991
