module

public import SignedDifferenceSets.Check

/-!
# N67: a (27, 14, 5) SDS in C₃ × C₃ × C₃

Open in Gordon's table (`SDS(27,14,5,[3,3,3])`, 2026-11-05). The set is object O9
(`objects/O9.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N67

/-- Object O9: the sign of each element, first coordinate outermost. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 → SignType := fun p =>
  (![![![1, 0, 0], ![0, 0, 0], ![0, 0, 1]],
    ![![0, 0, 0], ![0, 1, 1], ![1, 1, 1]],
    ![![0, 1, 1], ![-1, 1, 1], ![1, 1, 0]]])
    p.1 p.2.1 p.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS 14 5 sds := by decide

/-- N67: C₃ × C₃ × C₃ has a signed difference set with parameters (27, 14, 5). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 14 5 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N67
