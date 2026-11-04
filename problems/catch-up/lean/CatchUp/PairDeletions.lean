module

public import CatchUp.Executable

/-!
# Pair-deleted sets can lose below half their size

C89 refuted. `{8..19}` minus the pairs `{11, 12}` and `{17, 18}` (8 numbers, deficit 2 < 8/2) is a
mover loss (`pair_deleted_loss_19`), as are the two later sets found by E29. By the verified
evaluator (`Position.eval_eq_value_aux`) and the kernel. Ported from the refuter's check.
-/

@[expose] public section

namespace CatchUp

set_option maxHeartbeats 4000000 in -- an eight-number position evaluated by the kernel
/-- **C89's counterexample**: `({8..19} ∖ {11, 12, 17, 18}, 2)` is a mover loss, from any score. -/
theorem pair_deleted_loss_19 (s : ℕ) :
    valueAux {8, 9, 10, 13, 14, 15, 16, 19} s (s + 2) false = .loss := by
  rw [← Position.eval_eq_value_aux _ s (s + 2) (by omega), Nat.add_sub_cancel_left]
  decide +kernel

set_option maxHeartbeats 4000000 in -- an eight-number position evaluated by the kernel
/-- E29's second loss, `({10..21} ∖ {16, 17, 19, 20}, 2)`. -/
theorem pair_deleted_loss_21 (s : ℕ) :
    valueAux {10, 11, 12, 13, 14, 15, 18, 21} s (s + 2) false = .loss := by
  rw [← Position.eval_eq_value_aux _ s (s + 2) (by omega), Nat.add_sub_cancel_left]
  decide +kernel

set_option maxHeartbeats 4000000 in -- an eight-number position evaluated by the kernel
/-- E29's third loss, `({11..22} ∖ {12, 13, 18, 19}, 2)`. -/
theorem pair_deleted_loss_22 (s : ℕ) :
    valueAux {11, 14, 15, 16, 17, 20, 21, 22} s (s + 2) false = .loss := by
  rw [← Position.eval_eq_value_aux _ s (s + 2) (by omega), Nat.add_sub_cancel_left]
  decide +kernel

/-- The first set is `{8..19}` with the pairs `{11, 12}` and `{17, 18}` deleted. -/
theorem pair_deleted_loss_19_shape :
    ({8, 9, 10, 13, 14, 15, 16, 19} : Finset ℕ) = Finset.Icc 8 19 \ {11, 12, 17, 18} := by
  decide

end CatchUp
