module

public import SignedDifferenceSets.Check

/-!
# N49: a (25, 12, 1) SDS in C₅ × C₅

Open in Gordon's table (`SDS(25,12,1,[5,5])`, 2026-11-05). The set is object O6
(`objects/O6.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N49

/-- Object O6: the sign of each element, first coordinate outermost. -/
def sds : ZMod 5 × ZMod 5 → SignType := fun p =>
  (![![1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1],
    ![0, 1, 0, -1, -1],
    ![1, 1, 0, 1, 0],
    ![0, 1, -1, 1, 1]])
    p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS 12 1 sds := by decide

/-- N49: C₅ × C₅ has a signed difference set with parameters (25, 12, 1). -/
theorem hasSDS : HasSDS (ZMod 5 × ZMod 5) 12 1 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N49
