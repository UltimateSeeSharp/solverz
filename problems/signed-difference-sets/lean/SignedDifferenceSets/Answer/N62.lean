module

public import SignedDifferenceSets.Check

/-!
# N62: a (27, 10, 1) SDS in C₃ × C₉

Open in Gordon's table (`SDS(27,10,1,[3,9])`, 2026-11-05). The set is object O8
(`objects/O8.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N62

/-- Object O8: the sign of each element, first coordinate outermost. -/
def sds : ZMod 3 × ZMod 9 → SignType := fun p =>
  (![![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, -1],
    ![0, 1, -1, 1, 1, 1, 0, 1, 0]])
    p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS 10 1 sds := by decide

/-- N62: C₃ × C₉ has a signed difference set with parameters (27, 10, 1). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 9) 10 1 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N62
