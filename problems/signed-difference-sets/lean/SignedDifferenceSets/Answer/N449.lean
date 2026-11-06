module

public import SignedDifferenceSets.SetCheck

/-!
# N449: a (54, 38, 2) SDS in C₃ × C₁₈

Open in Gordon's table (`SDS(54,38,2,[3,18])`, 2026-11-05). The set is object O101
(`objects/O101.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N449

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O101's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xd024c3d5b2fd

set_option linter.style.longLine false in
/-- Object O101's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x20004338284c02

/-- Object O101: the sign of each element. -/
def sds : ZMod 3 × ZMod 18 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 38 2 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 18)
    (P := plus) (N := minus) (by decide +kernel)

/-- N449: C₃ × C₁₈ has a signed difference set with
parameters (54, 38, 2). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 18) 38 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N449
