module

public import SignedDifferenceSets.Statement

/-!
# Deciding `IsSDS` and `HasSDS`

Decidability instances so `decide` checks a candidate set, or rules out every set on a
tiny group, by evaluating the definitions directly.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

instance (k : ℕ) (lam : ℤ) (D : G → SignType) : Decidable (IsSDS k lam D) := by
  unfold IsSDS; infer_instance

instance (k : ℕ) (lam : ℤ) : Decidable (HasSDS G k lam) := by
  unfold HasSDS; infer_instance

end SignedDifferenceSets
